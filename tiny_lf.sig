(* Jason Reed's Tiny LF, implementation by Jon Sterling *)

signature TINY_LF =
sig
  include LF_SYNTAX

  structure Exn :
  sig
    type error
    exception LfExn of error
    val description : error -> string

    val debug : (unit -> 'a) -> 'a
  end

  (* typing judgments *)
  val okCl : ctx -> class -> unit
  val chk : ctx -> ntm -> class -> unit
  val inf : ctx -> rtm -> rclass
  val chkSp : ctx -> spine -> ctx -> unit
  val ctx : ctx -> ctx -> unit
end