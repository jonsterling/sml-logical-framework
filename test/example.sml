structure Example =
struct

  structure Sg = 
  struct
    datatype constant = 
       ZE  | SU 
     | EXP | INH | LAM  | AP
     | NAT | ARR

    val toString = 
      fn EXP => "exp"
       | INH => "inh"
       | NAT => "nat"
       | ARR => "arr"
       | ZE => "ze"
       | SU => "su"
       | LAM => "lam"
       | AP => "ap"
  

    val eq : constant * constant -> bool = op=
    fun compare (o1, o2) = String.compare (toString o1, toString o2)
  end

  structure Sym = LfSymbolWithConstants (Sg)
  structure Syn = LfSyntax (Sym)
  structure TinyLf = LfTyping (Syn)

  open TinyLf Sym
  infix `@ \\ --> ==>

  val Exp = C Sg.EXP `@ []

  val Ze = C Sg.ZE `@ []
  val Nat = C Sg.NAT `@ []
  fun Su e = C Sg.SU `@ [[] \\ e]
  fun Lam (x, e) = C Sg.LAM `@ [[x] \\ e]
  fun Inh e = C Sg.INH `@ [[] \\ e]
  fun Arr (s, t) = C Sg.ARR `@ [[] \\ s, [] \\ t]

  val mySig : ctx = 
    [(C Sg.EXP, [] ==> TYPE),
     (C Sg.INH, [[] ==> `Exp] ==> TYPE),
     (C Sg.NAT, [] ==> `Exp),
     (C Sg.ZE, [] ==> `Exp),
     (C Sg.SU, [[] ==> `Exp] ==> `Exp),
     (C Sg.LAM, [[[] ==> `Exp] ==> `Exp] ==> `Exp)]


  structure Rules = 
  struct
    structure Lf = TinyLf
    datatype rule = NAT_Z | NAT_S | ARR_I | HYP of int
    val printRule = 
      fn NAT_Z => "nat/z"
       | NAT_S => "nat/s"
       | ARR_I => "arr/i"
       | HYP x => "hyp[" ^ Int.toString x ^ "]"

    type state = (Lf.var * Lf.class, Lf.ntm) Lf.binder
    type unnamer = Lf.var -> int option
    
    local
      open Lf infix \ `@ \\
    in

      fun Hyp (i : int) goal = 
        let
          val H \ (rcl : rclass) = Unbind.class goal
          val hyp as (z, hypcl) = List.nth (H, List.length H - 1 - i)
          val (Psi \ rcl') = Unbind.class hypcl
          val true = Eq.rclass (rcl, rcl')
          val xs = List.map #1 H
        in
          Psi \ (xs \\ (z `@ []))
        end

      fun NatZ goal =
        let
          val H \ `(C Sg.INH `@ [tyNat]) = Unbind.class goal 
          val [] \ (C Sg.NAT `@ []) = Unbind.ntm tyNat
          val xs = List.map #1 H
        in
          [] \ (xs \\ Ze)
        end

      fun NatS goal =
        let
          val H \ `(C Sg.INH `@ [tyNat]) = Unbind.class goal 
          val [] \ (C Sg.NAT `@ []) = Unbind.ntm tyNat
          val xs = List.map #1 H

          val X = Sym.named "X"
          val Psi = [(X, H --> `(Inh Nat))]
        in
          Psi \ (xs \\ Su (X `@ List.map eta H))
        end

      fun ArrI goal =
        let
          val H \ ` (C Sg.INH `@ [tyArr]) = Unbind.class goal
          val [] \ (C Sg.ARR `@ [tyA, tyB]) = Unbind.ntm tyArr
          val [] \ tyA = Unbind.ntm tyA
          val [] \ tyB = Unbind.ntm tyB

          val X = Sym.named "X"
          val x = Sym.named "x"

          val H' = H @ [(x, [] ==> `(Inh tyA))]
          val Psi = [(X, H' --> `(Inh tyB))]

          val xs = List.map #1 H
          val lam = xs \\ (Lam (x, X `@ List.map eta H'))
        in
          Psi \ lam
        end
    end

    val rule = 
      fn NAT_Z => NatZ 
       | NAT_S => NatS
       | ARR_I => ArrI
       | HYP x => Hyp x
  end

  structure Refiner = LfRefiner (Rules)

  fun test () = 
    let
      open Refiner Rules
      val >> = SEQ infixr >>

      val script =
        ALL (RULE ARR_I)
        >> DEBUG "arr/i"
        >> ALL (RULE NAT_S)
        >> DEBUG "nat/s"
        >> ALL (RULE (HYP 0))
        >> DEBUG "hyp"

      val goal = [] ==> `(Inh (Arr (Nat, Nat)))
      val machine = init (MT script) goal
    in
      eval machine
    end

  val _ = LfExn.debug test

end