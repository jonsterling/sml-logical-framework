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
  infix 3 `@
  infixr 2 \ \\ --> ==>

  val Exp = C Sg.EXP `@ []

  val Ze = C Sg.ZE `@ []
  val Nat = C Sg.NAT `@ []
  fun Su e = C Sg.SU `@ [[] \\ e]
  fun Lam (x, e) = C Sg.LAM `@ [[x] \\ e]
  fun Inh e = C Sg.INH `@ [[] \\ e]
  fun Arr (s, t) = C Sg.ARR `@ [[] \\ s, [] \\ t]
  fun Ap (e1, e2) = C Sg.AP `@ [[] \\ e1, [] \\ e2]

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
    datatype rule = NAT_Z | NAT_S | ARR_I | ARR_E of Lf.var | HYP of Lf.var
    val printRule = 
      fn NAT_Z => "nat/z"
       | NAT_S => "nat/s"
       | ARR_I => "arr/i"
       | ARR_E z => "arr/e[" ^ Lf.Sym.toString z ^ "]"
       | HYP x => "hyp[" ^ Lf.Sym.toString x ^ "]"

    type goal = (Lf.var * Lf.class, Lf.rclass) Lf.bind
    type state = (Lf.var * goal, Lf.ntm) Lf.bind 
    type names = unit -> Lf.var

   fun prependHyps (H : ctx) (cl : class) : goal = 
      let
        val Psi \ rcl = Unbind.class cl
      in
        H @ Psi \ rcl
      end

    fun Hyp (z  : var) (H \ rcl : goal) = 
      let
        val hypcl = Inf.var H z
        val Psi \ rcl' = Unbind.class hypcl
        val Psi' = map (fn (x, cl : class) => (x, prependHyps H cl)) Psi
        val true = Eq.rclass (rcl, rcl')
      in
        Psi' \ map #1 H \\ z `@ map (fn (x, H \ rcl) => eta (x, H --> rcl)) Psi'
      end

    fun NatZ (H \ `inh) =
      let
        val C Sg.INH `@ [[] \ C Sg.NAT `@ []] = Unbind.rtm inh
        val xs = map #1 (H : ctx)
      in
        [] \ xs \\ Ze
      end

    fun NatS (H \ `inh) =
      let
        val C Sg.INH `@ [[] \ C Sg.NAT `@ []] = Unbind.rtm inh
        val X = Sym.new ()
        val Psi = [(X, H \ `(Inh Nat))]
      in
        Psi \ map #1 H \\ Su (X `@ map eta H)
      end

    fun ArrI x (H \ `inh) =
      let
        val C Sg.INH `@ [[] \ arr] = Unbind.rtm inh
        val C Sg.ARR `@ [[] \ tyA, [] \ tyB] = Unbind.rtm arr

        val X = Sym.new ()

        val Hx = H @ [(x, [] ==> `(Inh tyA))]
        val Psi = [(X, Hx \ `(Inh tyB))]
      in
        Psi \ map #1 H \\ Lam (x, X `@ map eta Hx)
      end
    
    fun ArrE z z' (H \ rcl : goal) = 
      let
        val (H0, hypcl, H1) = Ctx.split H z
        val Psi \ ` inh = Unbind.class hypcl
        val C Sg.INH `@ [[] \ arr] = Unbind.rtm inh
        val C Sg.ARR `@ [[] \ tyA, [] \ tyB] = Unbind.rtm arr

        val x = Sym.new ()
        val clx = [] ==> `(Inh tyA)

        val z'lam = map #1 Psi \\ Lam (x, z' `@ (map eta Psi @ [eta (x, clx)]))
        val rhoz = Sym.Env.singleton z z'lam
        val H1' = SubstN.ctx rhoz H1
        val rcl' = SubstN.rclass rhoz rcl

        val H' = H0 @ (z, hypcl) :: (z', Psi @ [(x, clx)] --> `(Inh tyB)) :: H1'

        val X = Sym.new ()

        val abs = (map #1 Psi @ [x]) \\ Ap (z `@ map eta Psi, x `@ [])
        val ns = map eta (H0 @ [(z, hypcl)]) @ abs :: map eta H1'
      in
        [(X, H' \ rcl')] \ map #1 H' \\ X `@ ns
      end

    fun rule fresh = 
      fn NAT_Z => NatZ
       | NAT_S => NatS
       | ARR_I => ArrI (fresh ())
       | ARR_E z => ArrE z (fresh ())
       | HYP x => Hyp x
  end

  structure Refiner = LfRefiner (Rules)

  fun runMachine {script, goal} = 
    Refiner.eval (Refiner.init (Refiner.MT script) goal)

  fun test () = 
    let
      open Refiner Rules

      (* SEQ is to THEN as kleisli composition is to kleisli extension. *)
      fun sequence [x] = x
        | sequence (x :: xs) = SEQ (x, sequence xs)
        | sequence [] = EACH []

      (* BIND pushes a block of user-chosen names for part of a tactic script; when the 
         sub-script is finished, this block will be popped. Tactics can eat names from outer 
         blocks. *)
      val >>> = BIND
      infix >>>

      fun elaborate r = 
        case Unbind.rtm r of 
           C Sg.LAM `@ [[x] \ r] => [x] >>> sequence [ALL (RULE ARR_I), DEBUG "lam", elaborate r]
         | C Sg.ZE `@ [] => sequence [ALL (RULE NAT_Z), DEBUG "nat/z"]
         | C Sg.SU `@ [[] \ r] => sequence [ALL (RULE NAT_S), DEBUG "nat/s", elaborate r]
           (* A fancy elaboration rule which accounts for higher-order hypotheses! Useful in case of funsplit, etc.: *)
         | (x as I _) `@ bs =>
             sequence
               [ALL (RULE (HYP x)), 
                DEBUG "hyp", 
                EACH (map (fn (xs \ r) => MT (xs >>> elaborate r)) bs)]

      val x = Sym.named "my-var"
      val f = Sym.named "f"

      val testElaborate = 
        {goal = [] \ `(Inh (Arr (Nat, Nat))),
         script = elaborate (Lam (x, Su (Su (x `@ []))))}

      val testFunSplit = 
        {goal = [] \ `(Inh (Arr (Arr (Nat, Nat), Nat))),
         script = 
           [x,f] >>> sequence 
            [DEBUG "start",
             ALL (RULE ARR_I),
             DEBUG "arr/i",
             ALL (RULE (ARR_E x)),
             DEBUG "arr/e",
             ALL (RULE (HYP f)),
             DEBUG "hyp",
             ALL (RULE NAT_S),
             DEBUG "su",
             ALL (RULE NAT_Z),
             DEBUG "ze"]}
    in
      print ("TESTING ELABORATION\n---------------------\n");
      runMachine testElaborate;
      print ("\n\n\nTESTING FUNSPLIT\n---------------------\n");
      runMachine testFunSplit
    end

  fun debug x = 
    LfExn.debug x 
    handle Refiner.Exn.Refine err => 
      (print ("\n\n" ^ Refiner.Exn.description err ^ "\n\n");
       raise Refiner.Exn.Refine err)

  val _ = debug test

end