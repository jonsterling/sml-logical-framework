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
  structure Eq :
  sig 
    val rclass : rclass * rclass -> bool
    val class : class * class -> bool
    val rtm : rtm * rtm -> bool
    val ntm : ntm * ntm -> bool
    val spine : spine * spine -> bool 
    val ctx : ctx * ctx -> bool
  end

  (* capture-avoiding renaming *)
  structure Ren : 
  sig
    type ren = var Sym.Env.dict
    val rclass : ren -> rclass -> rclass
    val class : ren -> class -> class
    val rtm : ren -> rtm -> rtm 
    val ntm : ren -> ntm -> ntm
    val spine : ren -> spine -> spine 
    val ctx : ren -> ctx -> ren * ctx

    val rebindCtx : var list -> ctx -> ren * ctx
  end

  (* capture-avoiding substitution *)
  structure Subst : 
  sig
    type env = ntm Sym.Env.dict
    val rclass : env -> rclass -> rclass
    val class : env -> class -> class
    val rtm : env -> rtm -> rtm
    val ntm : env -> ntm -> ntm
    val spine : env -> spine -> spine 
    val ctx : env -> ctx -> ctx

    val zipSpine : var list * spine -> env
  end

  structure Print : 
  sig
    val rclass : rclass -> string
    val class : class -> string
    val rtm : rtm -> string
    val ntm : ntm -> string 
    val spine : spine -> string 
    val ctx : ctx -> string
  end
end
