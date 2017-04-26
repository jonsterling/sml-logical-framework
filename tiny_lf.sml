structure Sym = Symbol ()

structure TinyLf : TINY_LF =
struct
  type var = Sym.symbol

  datatype rclass = 
     ` of rtm 
   | TYPE
  and class = PI of ctx * rclass
  and rtm = `@ of var * spine
  and ntm = \\ of var list * rtm
  withtype spine = ntm list
  and ctx = (var * class) list


  infix `@ \\


  fun toStringCl (PI (ctx, rcl)) = 
    "{" ^ toStringCtx ctx ^ "}" ^ toStringRcl rcl

  and toStringCtx psi = 
    case psi of
       [] => "-"
     | (x, cl) :: [] => Sym.toString x ^ ":" ^ toStringCl cl
     | (x, cl) :: psi' => Sym.toString x ^ ":" ^ toStringCl cl ^ "," ^ toStringCtx psi

  and toStringRcl rcl = 
    case rcl of 
       `r => toStringRtm r
     | TYPE => "*"

  and toStringRtm (x `@ sp) = 
    Sym.toString x ^ "[" ^ toStringSp sp ^ "]"

  and toStringSp sp = 
    case sp of 
       [] => "-"
     | n :: [] => toStringNtm n
     | n :: sp => toStringNtm n ^ "," ^ toStringSp sp
    
  and toStringNtm (xs \\ r) = 
    "[" ^ toStringVars xs ^ "]" ^ toStringRtm r
  
  and toStringVars xs = 
    case xs of 
       [] => ""
     | x :: [] => Sym.toString x
     | x :: xs => Sym.toString x ^ "," ^ toStringVars xs

  type eq_env = var Sym.Env.dict * var Sym.Env.dict
  val emptyEqEnv = (Sym.Env.empty, Sym.Env.empty)

  fun unifyVars (rho1, rho2) (x1, x2) = 
    let
      val z = Sym.new ()
    in
      (Sym.Env.insert rho1 x1 z, Sym.Env.insert rho2 x2 z)
    end

  val unifyBinders : eq_env -> var list * var list -> eq_env = 
    ListPair.foldlEq
      (fn (x1, x2, (rho1, rho2)) => 
         unifyVars (rho1, rho2) (x1, x2))

  fun lookupVar rho x = 
    Sym.Env.lookup rho x
    handle _ => x

  fun envFromSpine (sp, xs) = 
    ListPair.foldr
      (fn (x, n, rho) => Sym.Env.insert rho x n)
      Sym.Env.empty
      (xs, List.rev sp)

  fun eqVar (rho1, rho2) (x1, x2) = 
    lookupVar rho1 x1 = lookupVar rho2 x2

  fun renCl rho (PI (psi, rcl)) =
    let
      val (rho', psi') = renCtx rho psi
      val rcl' = renRcl rho' rcl
    in
      PI (psi', rcl')
    end
  and renRcl rho = 
    fn TYPE => TYPE
     | `r => ` (renRtm rho r)
  and renRtm rho (x `@ sp)  =
    lookupVar rho x `@ renSp rho sp
  and renSp rho = List.map (renNtm rho)
  and renNtm rho (xs \\ r) = 
    xs \\ renRtm (List.foldl (fn (x, rho) => Sym.Env.remove rho x) rho xs) r
  and renCtx rho psi =
    let
      fun go rho [] psi = (rho, psi)
        | go rho ((x, cl) :: psi) psi' = go (Sym.Env.remove rho x) psi ((x, renCl rho cl) :: psi')

      val (rho', psi') = go rho psi []
    in
      (rho', List.rev psi')
    end

  fun substCl rho (PI (psi, rcl)) =
    PI (substCtx rho psi, substRcl rho rcl)
  and substCtx rho psi =
    case psi of 
       [] => []
     | (x, cl) :: psi' => (x, substCl rho cl) :: substCtx (Sym.Env.remove rho x) psi'
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

  fun rebindCtx (xs, psi) = 
    let
      fun go rho [] [] out = (rho, out)
        | go rho (x :: xs) ((y, cl) :: psi) out =
            go (Sym.Env.insert rho y x) xs psi ((x, renCl rho cl) :: out)
        | go _ _ _ _ = raise Fail "Incorrect length of contexts"
      val (rho', psi') = go Sym.Env.empty xs psi []
    in
      (rho', List.rev psi')
    end


  fun eqClAux env (PI (psi1, rcl1), PI (psi2, rcl2)) : bool =
    case eqCtxAux env (psi1, psi2) of 
       SOME env' => eqRclAux env' (rcl1, rcl2) 
     | NONE => false

  and eqCtxAux env = 
    let
      exception CtxNotEq
      fun go env ([], []) = env
        | go env ((x1, cl1) :: psi1, (x2, cl2) :: psi2) =
            if eqClAux env (cl1, cl2) then 
              go (unifyVars env (x1, x2)) (psi1, psi2)
            else
              raise CtxNotEq
        | go _ _ = raise CtxNotEq
    in
      fn psis =>
        SOME (go env psis)
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

  fun findVar gm x = 
    let
      fun go [] = NONE 
        | go ((y, cl) :: gm') = if x = y then SOME cl else go gm' 
    in
      go (List.rev gm)
    end

  fun ensure b msg = 
    if b then 
      ()
    else
      raise Fail msg

  fun okCl gm (PI (psi, rcl)) =
    let
      val _ = ctx gm psi
    in
      case rcl of 
         ` r => ensure (eqRcl (inf (gm @ psi) r, TYPE)) "Expected TYPE"
       | TYPE => ()
    end

  and chk gm (xs \\ r) (PI (psi, rcl)) =
    let
      val (rho, psi') = rebindCtx (xs, psi)
      val rcl' = renRcl rho rcl
    in
      ensure (eqRcl (inf (gm @ psi') r, rcl')) "Error checking lambda"
    end

  and inf gm (x `@ sp) : rclass =
    case findVar gm x of 
       SOME (PI (psi, rcl)) =>
         (chkSp gm sp psi;
          substRcl (envFromSpine (sp, List.map #1 psi)) rcl)
     | NONE => raise Fail "Could not find variable"

  and chkSp gm (sp : spine) psi : unit =
    case (sp, psi) of 
       ([], []) => ()
     | (n :: sp', (x, cl) :: psi') =>
         let
           val rho = envFromSpine (sp', List.map #1 psi')
         in
           chk gm n (substCl rho cl);
           chkSp gm sp' psi'
         end
     | _ => raise Fail ("chkSp length mismatch: " ^ toStringSp sp ^ " / " ^ toStringCtx psi)

  and ctx gm psi = 
    case ListUtil.unsnoc psi of 
       NONE => ()
     | SOME (psi', (x, cl)) => 
       (ctx gm psi';
        okCl (gm @ psi') cl)
end