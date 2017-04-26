signature LF_SYNTAX = 
sig
  structure Sym : SYMBOL
  type var = Sym.symbol

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
  val eqSp : spine * spine -> bool
  val eqCtx : ctx * ctx -> bool

  type env = ntm Sym.Env.dict
  val substRcl : env -> rclass -> rclass
  val substCl : env -> class -> class
  val substRtm : env -> rtm -> rtm
  val substNtm : env -> ntm -> ntm
  val substSp : env -> spine -> spine 
  val substCtx : env -> ctx -> ctx

  type ren = var Sym.Env.dict
  val renRcl : ren -> rclass -> rclass
  val renCl : ren -> class -> class
  val renRtm : ren -> rtm -> rtm 
  val renNtm : ren -> ntm -> ntm
  val renSp : ren -> spine -> spine 
  val renCtx : ren -> ctx -> ren * ctx

  (* printing *)
  val toStringRcl : rclass -> string
  val toStringCl : class -> string
  val toStringRtm : rtm -> string
  val toStringNtm : ntm -> string 
  val toStringSp : spine -> string 
  val toStringCtx : ctx -> string
end
