structure Example =
struct

  structure Sg = 
  struct
    datatype constant = 
       NAT  | ZE  | SU 
     | LAM  | AP

    val toString = 
      fn NAT => "nat"
       | ZE => "ze"
       | SU => "su"
       | LAM => "lam"
       | AP => "ap"

    val eq : constant * constant -> bool = op=
    fun compare (o1, o2) = String.compare (toString o1, toString o2)
  end

  structure Sym = SymbolWithConstants (Sg)
  structure TinyLf = TinyLf (Sym)

  open TinyLf
  infix `@ \\

  val Nat = (Sym.C Sg.NAT `@ [])
  val Ze = Sym.C Sg.ZE `@ []
  fun Su x = Sym.C Sg.SU `@ [[] \\ x]

  val ==> = PI
  infix ==>

  val x = Sym.new ()

  val sigNat : ctx = 
    [(Sym.C Sg.NAT, [] ==> TYPE),
     (Sym.C Sg.ZE, [] ==> `Nat),
     (Sym.C Sg.SU, [(x, [] ==> `Nat)] ==> ` Nat)]

  val _ = ctx sigNat

  val three = Su (Su (Su Ze))
  val threeTy = inf sigNat three
  val _ = print (toStringRtm three ^ " : " ^ toStringRcl threeTy)
end