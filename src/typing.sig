signature LF_TYPING = 
sig
  include LF_SYNTAX
  structure LfExn : LF_EXN_UTIL

  structure Inf :
  sig
    val var : ctx -> var -> class
    val rtm : ctx -> rtm -> rclass
  end

  structure Chk : 
  sig
    val class : ctx -> class -> unit
    val ntm : ctx -> ntm -> class -> unit
    val spine : ctx -> spine -> ctx -> unit
    val ctx : ctx -> ctx -> unit
  end
end