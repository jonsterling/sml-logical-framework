signature LF_SYNTAX = 
sig
  structure Sym : LF_SYMBOL
  type var = Sym.symbol
  type 'a env = 'a Sym.Env.dict

  type 'v ntm_ (* normal terms *)
  type 'v spine_ = 'v ntm_ list
  type 'v class_ (* general classifiers *)
  type 'v ctx_ = ('v * 'v class_) list

  datatype ('v, 'a) app = `@ of 'v * 'a list
  datatype ('v, 'a) bind = \ of 'v list * 'a

  type 'v rtm_ = ('v, 'v ntm_) app (* atomic terms *)
  datatype 'v rclass_ = ` of 'v rtm_  | TYPE (* atomic classifiers *)

  type ntm = var ntm_
  type rtm = var rtm_
  type rclass = var rclass_
  type class = var class_
  type ctx = var ctx_
  type spine = var spine_

  val \\ : var list * rtm -> ntm
  val --> : ctx * rclass -> class
  val ==> : class list * rclass -> class

  val eta : var * class -> ntm


  structure Unbind :
  sig
    val ntm : ntm -> (var, rtm) bind
    val rtm : rtm -> (var, (var, rtm) bind) app
    val class : class -> (var * class, rclass) bind
  end

  structure Parsing : 
  sig
    val \\ : string list * string rtm_ -> string ntm_
    val --> : string ctx_ * string rclass_ -> string class_
    val ==> : string class_ list * string rclass_ -> string class_
  end

  structure Bind : 
  sig
    type bind_env
    type 'a m

    val run : 'a m -> 'a

    val var : string -> var m
    val rclass : string rclass_ -> rclass m
    val class : string class_ -> class m
    val ntm : string ntm_ -> ntm m
    val rtm : string rtm_ -> rtm m
    val spine : string spine_ -> spine m
    val ctx : string ctx_ -> ctx m
  end

  (* alpha equivalence *)
  structure Eq :
  sig
    val var : var * var -> bool
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
    type ren = var env
    val rclass : ren -> rclass -> rclass
    val class : ren -> class -> class
    val rtm : ren -> rtm -> rtm 
    val ntm : ren -> ntm -> ntm
    val spine : ren -> spine -> spine 
    val ctx : ren -> ctx -> ren * ctx

    val rebindCtx : var list -> ctx -> ren * ctx
  end

  (* capture-avoiding substitution *)
  structure SubstN : 
  sig
    val rclass : ntm env -> rclass -> rclass
    val class : ntm env -> class -> class
    val rtm : ntm env -> rtm -> rtm
    val ntm : ntm env -> ntm -> ntm
    val spine : ntm env -> spine -> spine 
    val ctx : ntm env -> ctx -> ctx

    val zipSpine : var list * spine -> ntm env
  end

  structure SubstRcl :
  sig
    type subst = (var, rclass) bind env
    val rclass : subst -> rclass -> rclass
    val class : subst -> class -> class
    val rtm : subst -> rtm -> rtm
    val ntm : subst -> ntm -> ntm
    val spine : subst -> spine -> spine 
    val ctx : subst -> ctx -> ctx
  end

  structure Print : 
  sig
    val var : var -> string
    val rclass : rclass -> string
    val class : class -> string
    val rtm : rtm -> string
    val ntm : ntm -> string 
    val spine : spine -> string
    val ctx : ctx -> string
  end

  structure Ctx :
  sig
    val split : ctx -> var -> ctx * class * ctx
  end
end
