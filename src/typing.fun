functor LfTyping (Syn : LF_SYNTAX) : LF_TYPING = 
struct
  open Syn
  infix `@ \ \\

  datatype error = 
      EXPECTED_TYPE of {expected : rclass, actual : rclass}
    | MISSING_VARIABLE of {var : var, ctx : ctx}
    | SPINE_MISMATCH of {spine : spine, ctx : ctx}


  datatype judgment = 
     OK_CLASS of ctx * class
   | CHK of ctx * ntm * class
   | INF of ctx * rtm
   | CHK_SP of ctx * spine * ctx
   | CTX of ctx * ctx
   | EQ of rclass * rclass
   | ERR of error
   | RET of rclass

  type metavar = var
  type history = judgment list
  type goal = metavar * history * judgment
  type stack = goal list

  val printError : error -> string = 
    fn EXPECTED_TYPE {expected, actual} =>
         "Got type [" ^ Print.rclass actual ^ "] but it should have been [" ^ Print.rclass expected ^ "]."
     | MISSING_VARIABLE {var, ctx} => 
         "Could not find variable [" ^ Print.var var ^ "] in context [" ^ Print.ctx ctx ^ "]."
     | SPINE_MISMATCH {spine, ctx} => 
         "The spine [" ^ Print.spine spine ^ "] could not be checked against a context of incorrect length, [" ^ Print.ctx ctx ^ "]."

  val printJudgment =
    fn OK_CLASS (Gamma, cl) => Print.ctx Gamma ^ " !- " ^ Print.class cl ^ " ok"
     | CHK (Gamma, n, cl) => Print.ctx Gamma ^ " !- " ^ Print.ntm n ^ " <= " ^ Print.class cl
     | INF (Gamma, r) => Print.ctx Gamma ^ " !- " ^ Print.rtm r ^ " => _"
     | CHK_SP (Gamma, sp, Psi) => Print.ctx Gamma ^ " !- [" ^ Print.spine sp ^ "] <= [" ^ Print.ctx Psi ^ "]"
     | CTX (Gamma, Psi) => Print.ctx Gamma ^ " !- " ^ Print.ctx Psi ^ " ctx"
     | EQ (rcl1, rcl2) => Print.rclass rcl1 ^ " == " ^ Print.rclass rcl2
     | ERR err => "throw {" ^ printError err ^ "}"
     | RET rcl => "return { " ^ Print.rclass rcl ^ "}"

  val rec printHistory = 
    fn [] => "(no history)"
     | [jdg] => "  - " ^ printJudgment jdg
     | jdg :: history => "  - " ^ printJudgment jdg ^ "\n" ^ printHistory history


  structure LfExn = 
  struct
    type error = error * history
    exception LfExn of error

    val description = 
      fn (error, []) => printError error
       | (error, history) => printError error ^ "\n\nHistory:\n" ^ printHistory history ^ "\n\n"
  end


  fun substJudgment (rho : SubstRcl.subst) : judgment -> judgment = 
    fn OK_CLASS (Gamma, cl) => OK_CLASS (SubstRcl.ctx rho Gamma, SubstRcl.class rho cl)
     | CHK (Gamma, n, cl) => CHK (SubstRcl.ctx rho Gamma, SubstRcl.ntm rho n, SubstRcl.class rho cl)
     | INF (Gamma, r) => INF (SubstRcl.ctx rho Gamma, SubstRcl.rtm rho r)
     | CHK_SP (Gamma, sp, Psi) => CHK_SP (SubstRcl.ctx rho Gamma, SubstRcl.spine rho sp, SubstRcl.ctx rho Psi)
     | CTX (Gamma, Psi) => CTX (SubstRcl.ctx rho Gamma, SubstRcl.ctx rho Psi)
     | EQ (rcl1, rcl2) => EQ (SubstRcl.rclass rho rcl1, SubstRcl.rclass rho rcl2)
     | RET rcl => RET (SubstRcl.rclass rho rcl)
     | ERR err => ERR err

  datatype 'a cfg = <: of 'a * stack
  infix <:

  fun findVar Gamma x = 
    let
      fun go [] = NONE
        | go ((y, cl) :: Gamma') = if Eq.var (x, y) then SOME cl else go Gamma' 
    in
      go (List.rev Gamma)
    end

  fun @@ (f, x) = f x
  infix 0 @@ 

  fun goal history jdg : goal =
    (Sym.new (), history, jdg)

  val step : stack -> stack = 
    fn (x, hist, jdg as OK_CLASS (Gamma, cl)) :: stk => 
       let
         val hist' = jdg :: hist
         val Psi \ rcl = Unbind.class cl
         val ctxGoal = goal (jdg :: hist) @@ CTX (Gamma, Psi)
       in
         case rcl of
            `r =>
            let
              val infGoal = goal hist' @@ INF (Gamma @ Psi, r)
              val eqGoal = goal hist' @@ EQ (` (#1 infGoal `@ []), TYPE)
            in
              ctxGoal :: infGoal :: eqGoal:: stk
            end
          | TYPE => ctxGoal :: stk
       end
     | (x, hist, jdg as CHK (Gamma, n, cl)) :: stk =>
       let
         val hist' = jdg :: hist
         val Psi \ rcl = Unbind.class cl
         val xs \ r = Unbind.ntm n
         val (rho, Psi') = Ren.rebindCtx xs Psi
         val rcl' = Ren.rclass rho rcl
         val infGoal = goal hist' @@ INF (Gamma @ Psi', r)
         val eqGoal = goal hist' @@ EQ (rcl', `(#1 infGoal `@ []))
       in
         infGoal :: eqGoal :: stk
       end
     | (x, hist, jdg as CHK_SP (Gamma, sp, Psi)) :: stk => 
        let
          val hist' = jdg :: hist
          val stk' =
            #1 @@ 
            ListPair.foldrEq
              (fn (n, (x,cl), (stk,rho)) =>
                 let
                   val cl' = SubstN.class rho cl
                   val rho' = Sym.Env.insert rho x n
                   val chkGoal = goal hist' @@ CHK (Gamma, n, cl')
                 in
                   (chkGoal :: stk, rho')
                 end)
              (stk, Sym.Env.empty)
              (sp, Psi)
            handle ListPair.UnequalLengths => 
              goal hist' (ERR (SPINE_MISMATCH {ctx = Psi, spine = sp})) :: stk
        in
          stk'
        end
     | (x, hist, jdg as INF (Gamma, y `@ sp)) :: stk =>
       (case findVar Gamma y of 
           SOME cl =>
           let
             val hist' = jdg :: hist
             val Psi \ rcl = Unbind.class cl
             val rcl' = SubstN.rclass (SubstN.zipSpine (List.map #1 Psi, sp)) rcl
             val chkGoal = goal hist' @@ CHK_SP (Gamma, sp, Psi)
             val rho = Sym.Env.insert Sym.Env.empty x ([] \ rcl')
             val stk' = List.map (fn (y, hist, jdg) => (y, List.map (substJudgment rho) hist, substJudgment rho jdg)) stk
           in
             chkGoal :: stk'
           end
         | NONE => goal (jdg :: hist) (ERR (MISSING_VARIABLE {var = x, ctx = Gamma})) :: stk)
     | (x, hist, jdg as CTX (Gamma, Psi)) :: stk =>
       (case ListUtil.unsnoc Psi of 
           NONE => stk
         | SOME (Psi', (x, cl)) => 
           let
             val hist' = jdg :: hist
             val ctxGoal = goal hist' @@ CTX (Gamma, Psi')
             val clGoal = goal hist' @@ OK_CLASS (Gamma @ Psi', cl)
           in
             ctxGoal :: clGoal :: stk
           end)
     | (x, hist, jdg as EQ (rcl1, rcl2)) :: stk =>
       if Eq.rclass (rcl1, rcl2) then 
         stk 
       else
         goal (jdg :: hist) (ERR (EXPECTED_TYPE {expected = rcl2, actual = rcl1})) :: stk
     | stk as (_, _, RET rcl) :: _ => stk
     | stk as (_, _, ERR _) :: _ => stk
     | [] => []

  val isFinal = 
    fn [] => true 
     | (_, _, RET _) :: _ => true
     | (_, _,ERR _) :: _ => true
     | _ => false


  fun eval stk = 
    if isFinal stk then 
      stk
    else
      eval (step stk)

  fun okCl Gamma cl = 
    case eval ([goal [] @@ OK_CLASS (Gamma, cl)]) of 
       (_, history, ERR err) :: _ => raise LfExn.LfExn (err, history)
     | _ => ()

  fun ctx Gamma Psi = 
    case eval ([goal [] @@ CTX (Gamma, Psi)]) of 
       (_, history, ERR err) :: _ => raise LfExn.LfExn (err, history)
     | _ => ()

  fun chk Gamma n cl = 
    case eval ([goal [] @@ CHK (Gamma, n, cl)]) of 
       (_, history, ERR err) :: _ => raise LfExn.LfExn (err, history)
     | _ => ()

  fun chkSp Gamma sp Psi = 
    case eval ([goal [] @@ CHK_SP (Gamma, sp, Psi)]) of 
       (_, history, ERR err) :: _ => raise LfExn.LfExn (err, history)
     | _ => ()
  
  fun inf Gamma r = 
    let
      val infGoal = goal [] @@ INF (Gamma, r)
      val retGoal = goal [] @@ RET (` (#1 infGoal `@ []))
    in
      case eval [infGoal, retGoal] of 
         (_, history, ERR err) :: _ => raise LfExn.LfExn (err, history)
       | [(_, _, RET rcl)] => rcl
       | _ => raise Fail "Internal error"
    end

  structure LfExn = LfExnUtil (LfExn)
end