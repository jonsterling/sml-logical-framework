functor LfSyntax (Sym : SYMBOL) : LF_SYNTAX = 
struct
  structure Sym = Sym
  type var = Sym.symbol

  (* atomic classifiers *)
  datatype rclass = 
     ` of rtm 
   | TYPE
  and class = PI of (var * class) list * rclass
  and rtm = `@ of var * ntm list
  and ntm = \\ of var list * rtm

  type spine = ntm list
  type ctx = (var * class) list
  type env = ntm Sym.Env.dict
  type ren = var Sym.Env.dict

  infix \\ `@

  fun unifyVars (rho1, rho2) (x1, x2) = 
    let
      val z = Sym.new ()
    in
      (Sym.Env.insert rho1 x1 z, Sym.Env.insert rho2 x2 z)
    end

  type eq_env = var Sym.Env.dict * var Sym.Env.dict
  val emptyEqEnv = (Sym.Env.empty, Sym.Env.empty)

  fun envFromSpine (sp, xs) = 
    ListPair.foldr
      (fn (x, n, rho) => Sym.Env.insert rho x n)
      Sym.Env.empty
      (xs, List.rev sp)

  val unifyBinders : eq_env -> var list * var list -> eq_env = 
    ListPair.foldlEq
      (fn (x1, x2, (rho1, rho2)) => 
         unifyVars (rho1, rho2) (x1, x2))



  fun lookupVar rho x = 
    Sym.Env.lookup rho x
    handle _ => x

  fun eqVar (rho1, rho2) (x1, x2) = 
    Sym.eq (lookupVar rho1 x1, lookupVar rho2 x2)

  fun eqClAux env (PI (Psi1, rcl1), PI (Psi2, rcl2)) : bool =
    case eqCtxAux env (Psi1, Psi2) of 
       SOME env' => eqRclAux env' (rcl1, rcl2) 
     | NONE => false

  and eqCtxAux env = 
    let
      exception CtxNotEq
      fun go env ([], []) = env
        | go env ((x1, cl1) :: Psi1, (x2, cl2) :: Psi2) =
            if eqClAux env (cl1, cl2) then 
              go (unifyVars env (x1, x2)) (Psi1, Psi2)
            else
              raise CtxNotEq
        | go _ _ = raise CtxNotEq
    in
      fn Psis =>
        SOME (go env Psis)
        handle CtxNotEq => NONE
    end

  and eqRclAux env (rcl1, rcl2) = 
    case (rcl1, rcl2) of 
       (` r1, ` r2) => eqRtmAux env (r1, r2)
     | (TYPE, TYPE) => true
     | _ => false
  
  and eqRtmAux env (x1 `@ sp1, x2 `@ sp2) = 
    eqVar env (x1, x2)
      andalso eqSpAux env (sp1, sp2)

  and eqSpAux env (sp1, sp2) = 
    case (sp1, sp2) of
       ([],[]) => true
     | (n1 :: sp1', n2 :: sp2') =>
         eqNtmAux env (n1, n2)
           andalso eqSpAux env (sp1', sp2')
     | _ => false

  and eqNtmAux env (xs1 \\ r1, xs2 \\ r2) =
    eqRtmAux
      (unifyBinders env (xs1, xs2))
      (r1, r2)

  val eqRcl = eqRclAux emptyEqEnv
  val eqNtm = eqNtmAux emptyEqEnv
  val eqSp = eqSpAux emptyEqEnv
  val eqRtm = eqRtmAux emptyEqEnv
  val eqCl = eqClAux emptyEqEnv
  val eqCtx = Option.isSome o eqCtxAux emptyEqEnv

  fun renCl rho (PI (Psi, rcl)) =
    let
      val (rho', Psi') = renCtx rho Psi
      val rcl' = renRcl rho' rcl
    in
      PI (Psi', rcl')
    end
  and renRcl rho = 
    fn TYPE => TYPE
     | `r => ` (renRtm rho r)
  and renRtm rho (x `@ sp)  =
    lookupVar rho x `@ renSp rho sp
  and renSp rho = List.map (renNtm rho)
  and renNtm rho (xs \\ r) = 
    xs \\ renRtm (List.foldl (fn (x, rho) => Sym.Env.remove rho x) rho xs) r
  and renCtx rho (Psi : ctx) =
    let
      fun go rho [] Psi = (rho, Psi)
        | go rho ((x, cl) :: Psi) Psi' = go (Sym.Env.remove rho x) Psi ((x, renCl rho cl) :: Psi')

      val (rho', Psi') = go rho Psi []
    in
      (rho', List.rev Psi')
    end

  fun substCl rho (PI (Psi, rcl)) =
    PI (substCtx rho Psi, substRcl rho rcl)
  and substCtx rho Psi =
    case Psi of 
       [] => []
     | (x, cl) :: Psi' => (x, substCl rho cl) :: substCtx (Sym.Env.remove rho x) Psi'
  and substRcl rho = 
    fn TYPE => TYPE
     | `r => ` (substRtm rho r)
  and substRtm rho (x `@ sp) =
    let
      val sp' = substSp rho sp
    in
      case Sym.Env.find rho x of 
        SOME (xs \\ r) =>
          let
            val rho' = envFromSpine (sp', xs)
          in
            substRtm rho' r
          end
       | NONE => x `@ sp'
    end
  and substNtm rho (xs \\ r) =
    xs \\ substRtm (List.foldl (fn (x, rho') => Sym.Env.remove rho' x) rho xs) r
  and substSp rho : spine -> spine = List.map (substNtm rho)

  fun toStringCl (PI (Psi, rcl)) = 
    case Psi of 
       [] => toStringRcl rcl
     | _ => "{" ^ toStringCtx Psi ^ "}" ^ toStringRcl rcl

  and toStringCtx Psi = 
    case Psi of
       [] => "-"
     | (x, cl) :: [] => Sym.toString x ^ ":" ^ toStringCl cl
     | (x, cl) :: Psi' => Sym.toString x ^ ":" ^ toStringCl cl ^ ", " ^ toStringCtx Psi'

  and toStringRcl rcl = 
    case rcl of 
       `r => toStringRtm r
     | TYPE => "*"

  and toStringRtm (x `@ sp) = 
    case sp of 
       [] => Sym.toString x
     | _ => Sym.toString x ^ "[" ^ toStringSp sp ^ "]"

  and toStringSp sp = 
    case sp of 
       [] => "-"
     | n :: [] => toStringNtm n
     | n :: sp => toStringNtm n ^ "," ^ toStringSp sp
    
  and toStringNtm (xs \\ r) = 
    case xs of 
       [] => toStringRtm r
     | _ =>  "[" ^ toStringVars xs ^ "]" ^ toStringRtm r
  
  and toStringVars xs = 
    case xs of 
       [] => ""
     | x :: [] => Sym.toString x
     | x :: xs => Sym.toString x ^ "," ^ toStringVars xs
end