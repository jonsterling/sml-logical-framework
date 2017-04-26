structure Example =
struct

  open TinyLf
  infix `@ \\

  val nat = Sym.named "nat"
  val ze = Sym.named "ze"
  val su = Sym.named "su"

  val Nat = (nat `@ [])
  val Ze = ze `@ []
  fun Su x = su `@ [[] \\ x]
  val ==> = PI
  infix ==>

  val x = Sym.new ()

  val sigNat : ctx = 
    [(nat, [] ==> TYPE),
     (ze, [] ==> `Nat),
     (su, [(x, [] ==> `Nat)] ==> ` Nat)]

  val _ = ctx sigNat

  val three = Su (Su (Su Ze))
  val threeTy = inf sigNat three
  val _ = print (toStringRtm three ^ " : " ^ toStringRcl threeTy)
end