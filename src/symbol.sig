signature LF_SYMBOL = 
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

signature LF_SYMBOL_WITH_CONSTANTS = 
sig
  type identifier
  type constant

  datatype ext_symbol = 
     C of constant 
   | I of identifier
  
  include LF_SYMBOL where type symbol = ext_symbol
end