signature SYMBOL = 
sig
  eqtype symbol
  val new : unit -> symbol
  val named : string -> symbol 
  val toString : symbol -> string
  
  structure Env : DICT where type key = symbol
end
