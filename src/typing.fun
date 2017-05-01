functor LfTyping (Syn : LF_SYNTAX) : LF_TYPING = 
struct
  open Syn

  fun @@ (f, x) = f x
  infix `@ \ \\ @@

  datatype error = 
     EXPECTED_TYPE of {expected : rclass, actual : rclass}
   | MISSING_VARIABLE of {var : var, ctx : ctx}
   | SPINE_MISMATCH of {spine : spine, ctx : ctx}

  (* The typechecker is organized as a machine using a variation on the Dependent LCF
     architecture, as described in Sterling/Harper 2017, but applied to a deterministic
     and syntax-directed logic. In this special case, there is only one primitive rule, 
     which can be thought of as a *local* version of the transition function for a 
     type-checking machine. *)

  datatype judgment = 
     OK_CLASS of ctx * class
   | CHK of ctx * ntm * class
   | INF of ctx * rtm
   | CHK_SP of ctx * spine * ctx
   | CTX of ctx * ctx
   | EQ of rclass * rclass

  (* Our machine has three instructions: we can push a judgment onto the stack,
     we can throw an error (aborting the process), or we can return. *)
  datatype 'a instr = 
     PUSH of judgment
   | THROW of error
   | RET of rclass

  type metavar = var
  type history = judgment list
  type goal = metavar * history * judgment instr
  type stack = goal list

  fun push jdg = (Sym.new (), PUSH jdg)
  fun throw err = (Sym.new (), THROW err)

  type synthesis = rclass option
  datatype 'a refine = |> of (metavar * 'a instr) list * synthesis
  infix |>

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

  val rec printHistory = 
    fn [] => "(no history)"
     | [jdg] => "  - " ^ printJudgment jdg
     | jdg :: history => "  - " ^ printJudgment jdg ^ "\n" ^ printHistory history

  fun substJudgment (rho : SubstRcl.subst) : judgment -> judgment = 
    fn OK_CLASS (Gamma, cl) => OK_CLASS (SubstRcl.ctx rho Gamma, SubstRcl.class rho cl)
     | CHK (Gamma, n, cl) => CHK (SubstRcl.ctx rho Gamma, SubstRcl.ntm rho n, SubstRcl.class rho cl)
     | INF (Gamma, r) => INF (SubstRcl.ctx rho Gamma, SubstRcl.rtm rho r)
     | CHK_SP (Gamma, sp, Psi) => CHK_SP (SubstRcl.ctx rho Gamma, SubstRcl.spine rho sp, SubstRcl.ctx rho Psi)
     | CTX (Gamma, Psi) => CTX (SubstRcl.ctx rho Gamma, SubstRcl.ctx rho Psi)
     | EQ (rcl1, rcl2) => EQ (SubstRcl.rclass rho rcl1, SubstRcl.rclass rho rcl2)

  fun substInstr (rho : SubstRcl.subst) : judgment instr -> judgment instr = 
     fn PUSH jdg => PUSH (substJudgment rho jdg)
      | THROW err => THROW err
      | RET rcl => RET (SubstRcl.rclass rho rcl)
  

  fun findVar Gamma x = 
    let
      fun go [] = NONE
        | go ((y, cl) :: Gamma') = if Eq.var (x, y) then SOME cl else go Gamma' 
    in
      go (List.rev Gamma)
    end

  (* The single primitive refinement rule for the Logical Framework. *)
  val refine : judgment -> judgment refine = 
    fn OK_CLASS (Gamma, cl) =>
       let
         val Psi \ rcl = Unbind.class cl
         val ctxGoal = push @@ CTX (Gamma, Psi)
       in
         case rcl of
            `r =>
            let
              val infGoal = push @@ INF (Gamma @ Psi, r)
              val eqGoal = push @@ EQ (` (#1 infGoal `@ []), TYPE)
            in
              [ctxGoal,infGoal,eqGoal] |> NONE
            end
          | TYPE => [ctxGoal] |> NONE
       end
     | CHK (Gamma, n, cl) => 
       let
         val Psi \ rcl = Unbind.class cl
         val xs \ r = Unbind.ntm n
         val (rho, Psi') = Ren.rebindCtx xs Psi
         val rcl' = Ren.rclass rho rcl
         val infGoal = push @@ INF (Gamma @ Psi', r)
         val eqGoal = push @@ EQ (rcl', `(#1 infGoal `@ []))
       in
         [infGoal, eqGoal] |> NONE
       end
     | CHK_SP (Gamma, sp, Psi) => 
       let
         val stk = 
           #1 @@ 
             ListPair.foldrEq
               (fn (n, (x,cl), (stk,rho)) =>
                   let
                     val cl' = SubstN.class rho cl
                     val rho' = Sym.Env.insert rho x n
                     val chkGoal = push @@ CHK (Gamma, n, cl')
                   in
                     (chkGoal :: stk, rho')
                   end)
               ([], Sym.Env.empty)
               (sp, Psi)
           handle ListPair.UnequalLengths => 
             [throw (SPINE_MISMATCH {ctx = Psi, spine = sp})]
       in
         stk |> NONE
       end
     | INF (Gamma, x `@ sp) =>
       (case findVar Gamma x of 
           SOME cl =>
           let
             val Psi \ rcl = Unbind.class cl
             val rcl' = SubstN.rclass (SubstN.zipSpine (List.map #1 Psi, sp)) rcl
             val chkGoal = push @@ CHK_SP (Gamma, sp, Psi)
           in
             [chkGoal] |> SOME rcl'
           end
         | NONE => [throw (MISSING_VARIABLE {var = x, ctx = Gamma})] |> NONE)
     | CTX (Gamma, Psi) =>
       (case ListUtil.unsnoc Psi of 
           NONE => [] |> NONE
         | SOME (Psi', (x, cl)) => 
           let
             val ctxGoal = push @@ CTX (Gamma, Psi')
             val clGoal = push @@ OK_CLASS (Gamma @ Psi', cl)
           in
             [ctxGoal, clGoal] |> NONE
           end)
     | EQ (rcl1, rcl2) =>
       if Eq.rclass (rcl1, rcl2) then 
         [] |> NONE
       else
         [throw (EXPECTED_TYPE {expected = rcl2, actual = rcl1})] |> NONE

  (* Next, we define the transition function for the machine; this can be thought of as a 
     strategy for deriving judgments in LF using the refinement rule that we have written 
     above. This hand-written strategy corresponds to "[refine, id...]" in Dependent LCF,
     the tactic that runs a rule on the *first subgoal*. *)
  local
    fun propagate (x : metavar) (synth : synthesis) (stk : stack) = 
      case synth of 
        SOME rcl =>
        let
          val rho = Sym.Env.insert Sym.Env.empty x ([] \ rcl)
        in
          List.map (fn (y, hist, instr) => (y, hist, substInstr rho instr)) stk
        end
      | NONE => stk
  in
    val step : stack -> stack option = 
      fn (x, hist, PUSH jdg) :: stk => 
        let
          val subgoals |> synthesis = refine jdg
          val subgoals' = List.map (fn (y, instr) => (y, jdg :: hist, instr)) subgoals
        in
          SOME (subgoals' @ propagate x synthesis stk)
        end
      | (_, _, THROW _) :: _ => NONE
      | (_, _, RET _) :: _ => NONE
      | [] => NONE
  end

  (* Finally, we define a routine to run our machine into quiescence. *)
  fun eval stk = 
    case step stk of 
       NONE => stk
     | SOME stk' => eval stk'


  structure LfExn = 
  struct
    type error = error * history
    exception LfExn of error

    val description = 
      fn (error, []) => printError error
       | (error, history) => printError error ^ "\n\nHistory:\n" ^ printHistory history ^ "\n\n"
  end

  fun init jdg = [(Sym.new (), [], PUSH jdg)]
  val run = eval o init

  fun okCl Gamma cl = 
    case run @@ OK_CLASS (Gamma, cl) of 
       (_, hist, THROW err) :: _ => raise LfExn.LfExn (err, hist)
     | _ => ()

  fun ctx Gamma Psi = 
    case run @@ CTX (Gamma, Psi)  of
       (_, hist, THROW err) :: _ => raise LfExn.LfExn (err, hist)
     | _ => ()

  fun chk Gamma n cl = 
    case run @@ CHK (Gamma, n, cl) of 
       (_, hist, THROW err) :: _ => raise LfExn.LfExn (err, hist)
     | _ => ()

  fun chkSp Gamma sp Psi = 
    case run @@ CHK_SP (Gamma, sp, Psi) of 
       (_, hist, THROW err) :: _ => raise LfExn.LfExn (err, hist)
     | _ => ()

  fun inf Gamma r = 
    let
      val infGoal = (Sym.new (), [], PUSH (INF (Gamma, r)))
      val retGoal = (Sym.new (), [], RET (` (#1 infGoal `@ [])))
    in
      case eval [infGoal, retGoal] of 
         (_, hist, THROW err) :: _ => raise LfExn.LfExn (err, hist)
       | (_, _, RET rcl) :: _ => rcl
       | _ => raise Fail "Internal error"
    end

  structure LfExn = LfExnUtil (LfExn)
end