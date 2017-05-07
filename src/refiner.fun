functor LfRefiner (R : LF_RULES) : LF_REFINER = 
struct
  structure Rules = R
  open R

  fun @@ (f, x) = f x
  infix @@

  exception todo fun ?e = raise e

  type names = int Lf.Sym.Env.dict

  datatype tactic =
     RULE of rule
   | MT of multitactic

  and multitactic = 
     ALL of tactic
   | EACH of tactic list
   | DEBUG of string
   | SEQ of multitactic * multitactic
   | ORELSE of multitactic * multitactic

  (* The refinement machine has four instructions:
       1. [MTAC mtac] means "run [mtac] on returned proof state"
       2. [AWAIT (x, mtac, st)] means "wait for [x] to emit a proof state, and merge it with [st], and continue executing with [mtac]"
       3. [PREPEND Psi] means "prepend the subgoals Psi onto the returned proof state"
       4. [HANDLE cfg] means "in case of an error, restore the machine state [cfg]"
   *)
  datatype instr =
     MTAC of multitactic
   | AWAIT of Lf.var * multitactic * state
   | PREPEND of (Lf.var * goal) list
   | HANDLE of machine_multi

  withtype stack = instr list

  and machine_focus = {tactic: tactic, goal: goal, stack: stack}
  and machine_multi = {multitactic: multitactic, state: state, stack: stack}
  and machine_retn = {state: state, stack: stack}
  and machine_throw = {exn: exn, goal: goal, trace: stack, stack: stack} 

  (* The refinement machine has four execution states:
       1. Executing a tactic on a focused goal
       2. Executing a multitactic on a proof state
       3. Returning a proof state
       4. Throwing an error
   *)
  datatype machine = 
     FOCUS of machine_focus
   | MULTI of machine_multi
   | RETN of machine_retn
   | THROW of machine_throw

  datatype 'a step = 
     STEP of 'a
   | FINAL of state
  
  fun init tac goal = 
    FOCUS
      {tactic = tac,
       goal = goal,
       stack = []}

  open Lf infix \ \\ `@ ==> -->

  fun cookGoal (Psi \ rcl) = 
    Psi --> rcl

  fun cookGoals Psi = 
    List.map (fn (x, goal) => (x, cookGoal goal)) Psi

  (* TODO: correct *)
  fun substGoal rho (Psi \ rclass) = 
    Psi \ SubstN.rclass rho rclass

  structure Print = 
  struct
    fun tactic tac = 
      case tac of 
         RULE rl => printRule rl
       | MT mtac => multitactic mtac
    
    and multitactic mtac = 
      case mtac of 
         ALL tac => tactic tac
       | EACH tacs => "[" ^ tactics tacs ^ "]"
       | DEBUG msg => "debug(\"" ^ msg ^ "\")"
       | SEQ (mtac1, mtac2) => multitactic mtac1 ^ "; " ^ multitactic mtac2
       | ORELSE (mtac1, mtac2) => "{" ^ multitactic mtac1 ^ "} | {" ^ multitactic mtac2 ^ "}"

    and tactics tacs = 
      case tacs of 
         [] => ""
       | [tac] => tactic tac 
       | tac :: tacs => tactic tac ^ ", " ^ tactics tacs
    
    fun state (Psi \ evd) = 
      Print.ctx (cookGoals Psi)
        ^ "\n   ===>  "
        ^ Print.ntm evd

    val instr = 
      fn MTAC mtac => "{" ^ multitactic mtac ^ "}"
       | AWAIT (x, mtac, st) => "await[" ^ Sym.toString x ^ "]{" ^ multitactic mtac ^ "}"
       | PREPEND Psi => "prepend{" ^ Print.ctx (cookGoals Psi) ^ "}"
       | HANDLE _ => "handler"

    fun stack stk = 
      case stk of 
         [] => "[]"
       | i :: stk => instr i ^ " :: " ^ stack stk
  end

  structure Exn = 
  struct
    type refine_error = exn * Lf.class * stack
    exception Refine of refine_error

    fun description (exn, goal, stack) = 
      "[ERROR] "
        ^ exnMessage exn
        ^ " when refining goal "
        ^ Lf.Print.class goal
        ^ "\n\nStack trace:\n"
        ^ Print.stack (List.rev stack)
  end

  fun goalToState (goal : goal) : state  = 
    let
      val x = Sym.new ()
    in
      [(x, goal)] \ eta (x, cookGoal goal)
    end

  fun stepFocus {tactic, goal, stack} : machine step = 
    case tactic of 
       RULE rl => 
         STEP @@
          (RETN {state = rule rl goal, stack = stack}
            handle exn =>
              THROW
                {exn = exn,
                goal = goal,
                trace = [],
                stack = stack})
     | MT mtac =>
         STEP o RETN @@
           {state = goalToState goal,
            stack = MTAC mtac :: stack}

  fun stepRetn {state as Psi \ evd, stack} : machine step = 
    case stack of 
       MTAC mtac :: stk =>
         STEP o MULTI @@
           {multitactic = mtac,
            state = state,
            stack = stk}

     | AWAIT (x, mtac, Psi' \ evd') :: stk =>
       let
         val rhox = Sym.Env.singleton x evd
         val Psi'' = List.map (fn (X, goal) => (X, substGoal rhox goal)) Psi'
         val evd'' = SubstN.ntm rhox evd'
       in
         STEP o MULTI @@
           {multitactic = mtac,
            state = Psi'' \ evd'',
            stack = PREPEND Psi :: stk}
       end

     | PREPEND Psi' :: stk =>
         STEP o RETN @@
           {state = Psi' @ Psi \ evd,
            stack = stk}

     | HANDLE _ :: stk => 
         STEP o RETN @@
           {state = state,
            stack = stk}

     | [] => FINAL state

  fun stepThrow {exn, goal, trace, stack} : machine step =
    case stack of 
       [] => raise Exn.Refine (exn, cookGoal goal, trace)
     | HANDLE multi :: stk => STEP @@ MULTI multi
     | instr :: stk =>
         STEP o THROW @@
           {exn = exn,
            goal = goal,
            trace = instr :: trace,
            stack = stk}

  fun debugString msg {state, stack} = 
    "[DEBUG] " ^ msg ^ "\n\n"
      ^ "Proof state: \n------------------------------\n"
      ^ Print.state state
      ^ "\n\nRemaining tasks: \n------------------------------\n"
      ^ Print.stack stack
      ^ "\n\n"

  fun stepMulti (multi as {multitactic, state as Psi \ evd, stack}) : machine step =
    case (Psi, multitactic) of 
       (_, DEBUG msg) =>
       let
         val retn = {state = state, stack = stack}
         val debugStr = debugString msg retn
       in 
         print debugStr;
         STEP @@ RETN retn
       end

     | (_, SEQ (mtac1, mtac2)) =>
       STEP o MULTI @@
         {multitactic = mtac1,
          state = state,
          stack = MTAC mtac2 :: stack}

     | ([], _) =>
       STEP o RETN @@
         {state = state,
          stack = stack}

     | ((x, goal) :: Psi, ALL tac) =>
       STEP o FOCUS @@
         {tactic = tac,
          goal = goal,
          stack = AWAIT (x, ALL tac, Psi \ evd) :: stack}

     | (_, EACH []) =>
       STEP o RETN @@
         {state = state,
          stack = stack}

     | ((x, goal) :: Psi, EACH (tac :: tacs)) =>
       STEP o FOCUS @@
         {tactic = tac,
          goal = goal,
          stack = AWAIT (x, EACH tacs, Psi \ evd) :: stack}

     | (_, ORELSE (mtac1, mtac2)) => 
       STEP o MULTI @@
         {multitactic = mtac1, 
          state = state,
          stack = HANDLE multi :: stack}

  val step : machine -> machine step = 
    fn FOCUS foc => stepFocus foc
     | MULTI multi => stepMulti multi
     | THROW throw => stepThrow throw
     | RETN retn => stepRetn retn

  fun eval m = 
    case step m of 
       STEP m => eval m
     | FINAL st => st
end