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
    datatype rule = NAT_Z | NAT_S | ARR_I
    val printRule = 
      fn NAT_Z => "nat/z"
       | NAT_S => "nat/s"
       | ARR_I => "arr/i"

    type state = (Lf.var * Lf.class, Lf.ntm) Lf.binder
    
    local
      open Lf infix \ `@ \\
    in
      fun NatZ goal =
        let
          val H \ `(C Sg.INH `@ [tyNat]) = Unbind.class goal 
          val [] \ (C Sg.NAT `@ []) = Unbind.ntm tyNat
          val xs = List.map #1 H
        in
          [] \ (xs \\ Ze)
        end

      fun NatS _ = raise Match

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

  end

  structure Refiner = LfRefiner (Rules)

  fun test () = 
    let
      open Refiner Rules
      val >> = SEQ infix >>
      val script =
        RULE ARR_I
        >> DEBUG "arr/i"
        >> EACH [RULE NAT_Z]
        >> DEBUG "nat/z"
      val machine = init script ([] ==> `(Inh (Arr (Nat, Nat))))
      val state = eval machine
    in
      ()
    end

  val _ = LfExn.debug test

end