functor Symbol () :> SYMBOL = 
struct
  type symbol = string * int

  val counter = ref 0

  fun named a = 
    let
      val i = !counter
    in
      counter := i + 1;
      (a, i)
    end

  fun new () = 
    named "?"

  fun toString (a, i) = 
    a

  structure Key =
  struct
    type t = symbol
    fun eq ((_,i), (_, j)) = i = j
    fun compare ((_,i), (_,j)) = Int.compare (i, j)
  end

  open Key
  structure Env = SplayDict (structure Key = Key)
end

signature SYMBOL_CONSTANT =
sig
  type constant
  val eq : constant * constant -> bool
  val compare : constant * constant -> order
  val toString : constant -> string
end

functor SymbolWithConstants(C : SYMBOL_CONSTANT) : SYMBOL_WITH_CONSTANTS where type constant = C.constant = 
struct
  structure Sym = Symbol ()
  type constant = C.constant
  type identifier = Sym.symbol

  datatype ext_symbol = 
     C of constant 
   | I of identifier

  type symbol = ext_symbol
  val new = I o Sym.new
  val named = I o Sym.named
  val toString = 
    fn C c => C.toString c 
     | I i => Sym.toString i

  structure Key = 
  struct
    type t = symbol
    val eq = 
      fn (C c1, C c2) => C.eq (c1, c2)
       | (I i1, I i2) => Sym.eq (i1, i2)
       | _ => false

    val compare = 
      fn (C c1, C c2) => C.compare (c1, c2)
       | (I i1, I i2) => Sym.compare (i1, i2)
       | (C _, I _) => GREATER
       | _ => LESS
  end

  open Key
  structure Env = SplayDict (structure Key = Key)
end