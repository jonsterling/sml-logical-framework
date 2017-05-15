functor LfSyntax (Sym : LF_SYMBOL) :> LF_SYNTAX where type Sym.symbol = Sym.symbol where type 'a Sym.Env.dict = 'a Sym.Env.dict =
struct
  structure Sym = Sym
  structure Env = Sym.Env

  type var = Sym.symbol
  type 'a env = 'a Sym.Env.dict

  datatype ('v, 'a) app = `@ of 'v * 'a list

  (* atomic classifiers *)
  datatype 'v rclass_ =
     ` of 'v rtm_
   | TYPE
  and ('a, 'b) bind = \ of 'a list * 'b
  and 'v class_ = PI of ('v * 'v class_, 'v rclass_) bind
  and 'v ntm_ = LAM of ('v, 'v rtm_) bind
  withtype 'v rtm_ = ('v, 'v ntm_) app

  type 'v spine_ = 'v ntm_ list
  type 'v ctx_ = ('v * 'v class_) list

  type ntm = var ntm_
  type rtm = var rtm_
  type rclass = var rclass_
  type class = var class_
  type ctx = var ctx_
  type spine = var spine_

  fun @@ (f, x) = f x
  infix 0 @@
  infix 1 \ \\ `@ --> ==>

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
    and ntm rho (LAM (xs \ r)) =
      LAM (xs \ rtm (List.foldl (fn (x, rho) => Sym.Env.remove rho x) rho xs) r)
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
    LAM (xs \ r)

  fun Psi --> rcl = 
    PI (Psi \ rcl)

  fun cls ==> cl = 
    List.map (fn x => (Sym.new (), x)) cls --> cl

  structure Unbind = 
  struct
    fun ntm (LAM (xs \ r)) = 
      let
        val xs' = List.map (Sym.named o Sym.name) xs
        val rho = ListPair.foldr (fn (x, x', rho) => Sym.Env.insert rho x x') Sym.Env.empty (xs, xs')
        val r' = Ren.rtm rho r
      in
        xs' \ r'
      end

    fun rtm (x `@ ns) = 
      x `@ List.map ntm ns

    fun class (PI (Psi \ rcl)) = 
      let
        val xs = List.map (Sym.named o Sym.name o #1) Psi
        val (rho, Psi') = Ren.rebindCtx xs Psi
        val rcl' = Ren.rclass rho rcl
      in
        Psi' \ rcl'
      end
  end

  structure Parsing = 
  struct
    val op\\ = op\\
    val op--> = op-->
    fun cls ==> cl = 
      List.map (fn x => ("_", x)) cls --> cl
  end

  structure Bind = 
  struct
    type bind_env = var StringListDict.dict

    (* assignment of identity to variables is performed in the state monad, so that we can give a single identity to *free* variables of the same name,
       without taking a context as input. *)
    type 'a m = bind_env -> 'a * bind_env

    fun ret a env = (a, env)
    fun >>= (m : 'a m, f : 'a -> 'b m) : 'b m = 
      fn env => 
        let
          val (a, env') = m env
        in
          f a env'
        end

    fun >> (m, n) = 
      >>= (m, fn _ => n)

    infixr >>= >>

    fun local_ (f : bind_env -> bind_env) (m : 'a m) : 'a m =  m o f
    fun addVars xs env = List.foldr (fn (x, env) => StringListDict.insert env (Sym.name x) x) env xs
    fun peek (xs : string list) (m : var list -> 'a m) : 'a m =
      let
        val xs' = List.map Sym.named xs
      in
        m xs' o addVars xs'
      end

    fun run (m : 'a m) : 'a = 
      #1 (m StringListDict.empty)

    fun var x : var m = 
      fn env => 
        case StringListDict.find env x of 
           SOME x' => (x', env)
         | NONE => 
           let
             val x' = Sym.named x
           in
             (x', StringListDict.insert env x x')
           end

    fun rclass rcl : rclass m = 
      case rcl of 
         TYPE => ret TYPE
       | ` r => rtm r >>= (fn r' => ret @@ ` r')

    and class (PI (Psi \ rcl)) : class m =
      ctx Psi >>= (fn Psi' => 
        peek (List.map #1 Psi) (fn xs => 
          let
            val (_, Psi'') = Ren.rebindCtx xs Psi'
          in
            rclass rcl >>= (fn rcl' => 
              ret @@ PI (Psi'' \ rcl'))
          end))

    and rtm (x `@ sp) : rtm m =
      var x >>= (fn x' => 
        spine sp >>= (fn sp' => 
          ret @@ x' `@ sp'))

    and ntm (LAM (xs \ r)) : ntm m  =
      peek xs (fn xs' => 
        rtm r >>= (fn r' => ret @@ LAM (xs' \ r')))

    and spine sp : spine m = 
      case sp of 
         [] => ret []
       | n::sp => 
           ntm n >>= (fn n' => 
             spine sp >>= (fn sp' => 
               ret @@ n' :: sp'))

    and ctx Psi : ctx m = 
      case Psi of 
         [] => ret []
       | (x,cl) :: Psi =>
         class cl >>= (fn cl' =>
           peek [x] (fn [x'] =>
             ctx Psi >>= (fn Psi' => 
               ret @@ (x', cl') :: Psi')))
  end

  fun eta (x : var, cl : class) : ntm = 
    let
      val Psi \ rcl = Unbind.class cl
      val xs = List.map eta Psi
    in
      List.map #1 Psi \\ (x `@ xs)
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

    and ntmAux env (LAM (xs1 \ r1), LAM (xs2 \ r2)) =
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
           SOME (LAM (xs \ r)) => rtm (zipSpine (xs, sp')) r
         | NONE => x `@ sp'
      end
    and ntm rho (LAM (xs \ r)) =
      LAM (xs \ rtm (List.foldl (fn (x, rho') => Sym.Env.remove rho' x) rho xs) r)
    and spine rho = List.map (ntm rho)
  end

  structure SubstRcl =
  struct
    type subst = (var, rclass) bind env

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
    and ntm rho (LAM (xs \ r)) =
      LAM (xs \ rtm (List.foldl (fn (x, rho') => Sym.Env.remove rho' x) rho xs) r)
    and spine rho = List.map (ntm rho)
  end

  structure Print =
  struct
    fun var x = 
      Sym.toString x

    fun vars xs =
      case xs of
         [] => ""
       | x :: [] => var x
       | x :: xs => var x ^ "," ^ vars xs

    fun class (PI (Psi \ rcl)) =
      case Psi of
         [] => rclass rcl
       | _ => "{" ^ ctx Psi ^ "}" ^ rclass rcl

    and ctx Psi =
      case Psi of
         [] => "-"
       | (x, cl) :: [] => var x ^ ":" ^ class cl
       | (x, cl) :: Psi' => var x ^ ":" ^ class cl ^ ", " ^ ctx Psi'

    and rclass rcl =
      case rcl of
         `r => rtm r
       | TYPE => "*"

    and rtm (x `@ sp) =
      case sp of
         [] => var x
       | _ => var x ^ "[" ^ spine sp ^ "]"

    and spine sp =
      case sp of
         [] => "-"
       | n :: [] => ntm n
       | n :: sp => ntm n ^ "," ^ spine sp

    and ntm (LAM (xs \ r)) =
      case xs of
         [] => rtm r
       | _ =>  "[" ^ vars xs ^ "]" ^ rtm r
  end

  structure Ctx = 
  struct
    fun splitAux Gamma0 Gamma1 x = 
      case Gamma1 of 
         [] => raise Fail "Variable not found"
       | (y, a) :: Gamma1 => if Sym.eq (x, y) then (Gamma0, a, Gamma1) else splitAux Gamma0 Gamma1 x

    fun split Gamma x = 
      let
        val (Gamma0, a, Gamma1) = splitAux [] Gamma x
      in
        (List.rev Gamma0, a, Gamma1)
      end
  end
end