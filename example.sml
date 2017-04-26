structure Example =
struct

  structure Sg = 
  struct
    datatype constant = 
       NAT  | ZE  | SU 
     | EXP | LAM  | AP
     | DIM | I0 | I1 | DIMABS | DIMAP

    val toString = 
      fn NAT => "nat"
       | EXP => "exp"
       | ZE => "ze"
       | SU => "su"
       | LAM => "lam"
       | AP => "ap"
       | DIM => "dim"
       | I0 => "0"
       | I1 => "1"
       | DIMABS => "dimabs"
       | DIMAP => "face"

    val eq : constant * constant -> bool = op=
    fun compare (o1, o2) = String.compare (toString o1, toString o2)
  end

  structure Sym = SymbolWithConstants (Sg)
  structure TinyLf = TinyLf (Sym)

  open TinyLf
  infix `@ \\

  val Nat = Sym.C Sg.NAT `@ []
  val Exp = Sym.C Sg.EXP `@ []
  val Dim = Sym.C Sg.DIM `@ []
  val I0 = Sym.C Sg.I0 `@ []
  val I1 = Sym.C Sg.I1 `@ []
  val Ze = Sym.C Sg.ZE `@ []
  fun Su e = Sym.C Sg.SU `@ [[] \\ e]
  fun Lam (x, e) = Sym.C Sg.LAM `@ [[x] \\ e]

  fun ==> (cls, rcl) = 
    PI (List.map (fn cl => (Sym.new (), cl)) cls, rcl)

  infix ==>

  val mySig : ctx = 
    [(Sym.C Sg.NAT, [] ==> TYPE),
     (Sym.C Sg.EXP, [] ==> TYPE),
     (Sym.C Sg.ZE, [] ==> `Nat),
     (Sym.C Sg.SU, [[] ==> `Nat] ==> `Nat),
     (Sym.C Sg.LAM, [[[] ==> `Exp] ==> `Exp] ==> `Exp),
     (Sym.C Sg.DIM, [] ==> TYPE),
     (Sym.C Sg.I0, [] ==> `Dim),
     (Sym.C Sg.I1, [] ==> `Dim),
     (Sym.C Sg.DIMABS, [[[] ==> `Dim] ==> `Exp] ==> `Exp),
     (Sym.C Sg.DIMAP, [[] ==> `Exp, [] ==> `Dim] ==> `Exp)]

  val three = Su (Su (Su Ze))
  val threeTy = inf mySig three
  val welp = ctx [] mySig
  val _ = print (toStringCtx mySig ^ "\n")
  val _ = print (toStringRtm three ^ " : " ^ toStringRcl threeTy ^ "\n")
end