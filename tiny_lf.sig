(* Jason Reed's Tiny LF, implementation by Jon Sterling *)


signature TINY_LF =
sig
  include LF_SYNTAX

  (* typing judgments *)
  val okCl : ctx -> class -> unit
  val chk : ctx -> ntm -> class -> unit
  val inf : ctx -> rtm -> rclass
  val chkSp : ctx -> spine -> ctx -> unit
  val ctx : ctx -> ctx -> unit
end