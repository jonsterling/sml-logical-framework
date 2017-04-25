(* Jason Reed's Tiny LF, implementation by Jon Sterling *)

signature TINY_LF =
sig
  type var

  (* atomic classifiers *)
  datatype rclass = 
     ` of rtm 
   | TYPE

  (* classifiers *)
  and class = PI of (var * class) list * rclass

  (* atomic terms *)
  and rtm = `@ of var * ntm list

  (* normal terms *)
  and ntm = \\ of var list * rtm

  type spine = ntm list
  type ctx = (var * class) list

  (* alpha equivalence *)
  val eqRcl : rclass * rclass -> bool
  val eqCl : class * class -> bool
  val eqRtm : rtm * rtm -> bool
  val eqNtm : ntm * ntm -> bool
  val eqSpine : spine * spine -> bool
  val eqCtx : ctx * ctx -> bool

  (* typing judgments *)
  val okCl : ctx -> class -> unit
  val chk : ctx -> ntm -> class -> unit
  val inf : ctx -> rtm -> rclass
  val chkSp : ctx -> spine -> ctx -> unit
  val ctx : ctx -> ctx -> unit
end