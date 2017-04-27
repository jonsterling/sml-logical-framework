signature SYMBOL = 
sig
  type symbol
  val eq : symbol * symbol -> bool
  val compare : symbol * symbol -> order

  val new : unit -> symbol
  val named : string -> symbol 
  val toString : symbol -> string
  val name : symbol -> string

  structure Env : DICT where type key = symbol
end

signature SYMBOL_WITH_CONSTANTS = 
sig
  type identifier
  type constant

  datatype ext_symbol = 
     C of constant 
   | I of identifier
  
  include SYMBOL where type symbol = ext_symbol
end