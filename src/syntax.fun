functor LfSyntax (Sym : LF_SYMBOL) :> LF_SYNTAX where type Sym.symbol = Sym.symbol where type 'a Sym.Env.dict = 'a Sym.Env.dict =
struct
  structure Sym = Sym
  structure Env = Sym.Env

  type var = Sym.symbol
  type 'a env = 'a Sym.Env.dict

  (* atomic classifiers *)
  datatype rclass =
     ` of rtm
   | TYPE
  and rtm = `@ of var * ntm list
  and ('a, 'b) binder = \ of 'a list * 'b
  and class = PI of (var * class, rclass) binder
  withtype ntm = (var, rtm) binder

  type spine = ntm list
  type ctx = (var * class) list

  infix \ \\ `@ --> ==>

  fun unifyVars (rho1, rho2) (x1, x2) =
    let
      val z = Sym.new ()
    in
      (Sym.Env.insert rho1 x1 z, Sym.Env.insert rho2 x2 z)
    end

  fun lookupVar rho x =
    Sym.Env.lookup rho x
    handle _ => x

  structure Ren =
  struct
    type ren = var env

    fun class rho (PI (Psi \ rcl)) =
      let
        val (rho', Psi') = ctx rho Psi
        val rcl' = rclass rho' rcl
      in
        PI (Psi' \ rcl')
      end
    and rclass rho =
      fn TYPE => TYPE
       | `r => ` (rtm rho r)
    and rtm rho (x `@ sp)  =
      lookupVar rho x `@ spine rho sp
    and spine rho = List.map (ntm rho)
    and ntm rho (xs \ r) =
      xs \ rtm (List.foldl (fn (x, rho) => Sym.Env.remove rho x) rho xs) r
    and ctx rho Psi =
      let
        fun go rho [] Psi = (rho, Psi)
          | go rho ((x, cl) :: Psi) Psi' = go (Sym.Env.remove rho x) Psi ((x, class rho cl) :: Psi')

        val (rho', Psi') = go rho Psi []
      in
        (rho', List.rev Psi')
      end

    fun rebindCtx xs Psi =
      let
        fun go rho [] [] out = (rho, out)
          | go rho (x :: xs) ((y, cl) :: Psi) out =
              go (Sym.Env.insert rho y x) xs Psi ((x, class rho cl) :: out)
          | go _ _ _ _ = raise Fail "Incorrect length of contexts"
        val (rho', Psi') = go Sym.Env.empty xs Psi []
      in
        (rho', List.rev Psi')
      end
  end

  fun xs \\ r = 
    xs \ r

  fun Psi --> rcl = 
    PI (Psi \ rcl)

  fun cls ==> cl = 
    List.map (fn x => (Sym.new (), x)) cls --> cl

  structure Unbind = 
  struct
    fun ntm (xs \ r) = 
      let
        val xs' = List.map (Sym.named o Sym.name) xs
        val rho = ListPair.foldr (fn (x, x', rho) => Sym.Env.insert rho x x') Sym.Env.empty (xs, xs')
        val r' = Ren.rtm rho r
      in
        xs' \ r'
      end

    fun class (PI (Psi \ rcl)) = 
      let
        val xs = List.map (Sym.named o Sym.toString o #1) Psi
        val (rho, Psi') = Ren.rebindCtx xs Psi
        val rcl' = Ren.rclass rho rcl
      in
        Psi' \ rcl'
      end
  end

  structure Eq =
  struct
    type env = var env * var env
    val emptyEqEnv = (Sym.Env.empty, Sym.Env.empty)

    val unifyBinders : env -> var list * var list -> env =
      ListPair.foldlEq
        (fn (x1, x2, (rho1, rho2)) =>
           unifyVars (rho1, rho2) (x1, x2))

    fun varAux (rho1, rho2) (x1, x2) =
      Sym.eq (lookupVar rho1 x1, lookupVar rho2 x2)

    fun classAux env (PI (Psi1 \ rcl1), PI (Psi2 \ rcl2)) =
      case ctxAux env (Psi1, Psi2) of
         SOME env' => rclassAux env' (rcl1, rcl2)
       | NONE => false

    and ctxAux env =
      let
        exception CtxNotEq
        fun go env ([], []) = env
          | go env ((x1, cl1) :: Psi1, (x2, cl2) :: Psi2) =
              if classAux env (cl1, cl2) then
                go (unifyVars env (x1, x2)) (Psi1, Psi2)
              else
                raise CtxNotEq
          | go _ _ = raise CtxNotEq
      in
        fn Psis =>
          SOME (go env Psis)
          handle CtxNotEq => NONE
      end

    and rclassAux env (rcl1, rcl2) =
      case (rcl1, rcl2) of
         (` r1, ` r2) => rtmAux env (r1, r2)
       | (TYPE, TYPE) => true
       | _ => false

    and rtmAux env (x1 `@ sp1, x2 `@ sp2) =
      varAux env (x1, x2)
        andalso spineAux env (sp1, sp2)

    and spineAux env (sp1, sp2) =
      case (sp1, sp2) of
         ([],[]) => true
       | (n1 :: sp1', n2 :: sp2') =>
           ntmAux env (n1, n2)
             andalso spineAux env (sp1', sp2')
       | _ => false

    and ntmAux env (xs1 \ r1, xs2 \ r2) =
      rtmAux
        (unifyBinders env (xs1, xs2))
        (r1, r2)

    val var = varAux emptyEqEnv
    val rclass = rclassAux emptyEqEnv
    val class = classAux emptyEqEnv
    val ntm  = ntmAux emptyEqEnv
    val spine = spineAux emptyEqEnv
    val rtm = rtmAux emptyEqEnv
    val ctx = Option.isSome o ctxAux emptyEqEnv
  end


  structure SubstN =
  struct
    fun zipSpine (xs, sp) =
      ListPair.foldr
        (fn (x, n, rho) => Sym.Env.insert rho x n)
        Sym.Env.empty
        (xs, sp)

    fun class rho (PI (Psi \ rcl)) =
      PI (ctx rho Psi \ rclass rho rcl)
    and ctx rho Psi =
      case Psi of
         [] => []
       | (x, cl) :: Psi' => (x, class rho cl) :: ctx (Sym.Env.remove rho x) Psi'
    and rclass rho =
      fn TYPE => TYPE
       | `r => ` (rtm rho r)
    and rtm rho (x `@ sp) =
      let
        val sp' = spine rho sp
      in
        case Sym.Env.find rho x of
           SOME (xs \ r) => rtm (zipSpine (xs, sp')) r
         | NONE => x `@ sp'
      end
    and ntm rho (xs \ r) =
      xs \ rtm (List.foldl (fn (x, rho') => Sym.Env.remove rho' x) rho xs) r
    and spine rho = List.map (ntm rho)
  end

  structure SubstRcl =
  struct
    type subst = (var, rclass) binder env

    fun class rho (PI (Psi \ rcl)) =
      PI (ctx rho Psi \ rclass rho rcl)
    and ctx rho Psi =
      case Psi of
         [] => []
       | (x, cl) :: Psi' => (x, class rho cl) :: ctx (Sym.Env.remove rho x) Psi'
    and rclass rho =
      fn TYPE => TYPE
       | `(x `@ sp) => 
         let
           val sp' = spine rho sp
         in
           case Sym.Env.find rho x of 
              SOME (xs \ rcl) => SubstN.rclass (SubstN.zipSpine (xs, sp')) rcl
            | NONE => `(x `@ sp')
         end
    and rtm rho (x `@ sp) =
      let
        val sp' = spine rho sp
      in 
        (* Is this correct? *)
        (x `@ sp')
      end
    and ntm rho (xs \ r) =
      xs \ rtm (List.foldl (fn (x, rho') => Sym.Env.remove rho' x) rho xs) r
    and spine rho = List.map (ntm rho)
  end

  structure Print =
  struct
    fun var x = 
      Sym.toString x

    fun vars xs =
      case xs of
         [] => ""
       | x :: [] => Sym.toString x
       | x :: xs => Sym.toString x ^ "," ^ vars xs

    fun class (PI (Psi \ rcl)) =
      case Psi of
         [] => rclass rcl
       | _ => "{" ^ ctx Psi ^ "}" ^ rclass rcl

    and ctx Psi =
      case Psi of
         [] => "-"
       | (x, cl) :: [] => Sym.toString x ^ ":" ^ class cl
       | (x, cl) :: Psi' => Sym.toString x ^ ":" ^ class cl ^ ", " ^ ctx Psi'

    and rclass rcl =
      case rcl of
         `r => rtm r
       | TYPE => "*"

    and rtm (x `@ sp) =
      case sp of
         [] => Sym.toString x
       | _ => Sym.toString x ^ "[" ^ spine sp ^ "]"

    and spine sp =
      case sp of
         [] => "-"
       | n :: [] => ntm n
       | n :: sp => ntm n ^ "," ^ spine sp

    and ntm (xs \ r) =
      case xs of
         [] => rtm r
       | _ =>  "[" ^ vars xs ^ "]" ^ rtm r
  end
end