(* Jason Reed's Tiny LF, implementation by Jon Sterling *)

signature TINY_LF =
sig
  type var

  type 'a ctx = (var * 'a) list

  (* atomic classifiers *)
  datatype rclass = 
     ` of rtm 
   | TYPE

  (* classifiers *)
  and class = PI of class ctx * rclass

  (* atomic terms *)
  and rtm = `@ of var * ntm list

  (* normal terms *)
  and ntm = \\ of var list * rtm

  type spine = ntm list

  (* alpha equivalence *)
  val eqRcl : rclass * rclass -> bool
  val eqCl : class * class -> bool
  val eqRtm : rtm * rtm -> bool
  val eqNtm : ntm * ntm -> bool
  val eqSpine : spine * spine -> bool
  val eqCtx : class ctx * class ctx -> bool

  (* typing judgments *)
  val okCl : class ctx -> class -> unit
  val chk : class ctx -> ntm -> class -> unit
  val inf : class ctx -> rtm -> rclass
  val chkSp : class ctx -> spine -> class ctx -> unit
  val ctx : class ctx -> class ctx -> unit
end