signature LF_SYNTAX_PRINT = 
sig
  include LF_SYNTAX

  val var : var -> string
  val rclass : rclass -> string
  val class : class -> string
  val rtm : rtm -> string
  val ntm : ntm -> string 
  val spine : spine -> string
  val ctx : ctx -> string
end
