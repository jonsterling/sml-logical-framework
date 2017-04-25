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

  structure Env = SplayDict (structure Key = Key)
end
