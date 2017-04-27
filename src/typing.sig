signature LF_TYPING = 
sig
  include LF_SYNTAX
  structure LfExn : LF_EXN_UTIL

  (* typing judgments *)
  val okCl : ctx -> class -> unit
  val chk : ctx -> ntm -> class -> unit
  val inf : ctx -> rtm -> rclass
  val chkSp : ctx -> spine -> ctx -> unit
  val ctx : ctx -> ctx -> unit
end