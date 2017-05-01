
functor LfRefiner (R : LF_RULES) : LF_REFINER = 
struct
  structure Rules = R
  open R

  exception todo fun ?e = raise e

  datatype tactic =
     RULE of rule
   | MT of multitactic

  and multitactic = 
     ALL of tactic
   | EACH of tactic list
   | DEBUG of string
   | SEQ of multitactic * multitactic
   | ORELSE of multitactic * multitactic

  datatype instr = 
     PUSH of multitactic
   | MTAC of Lf.var * multitactic * state
   | PREPEND of Lf.ctx
   | HANDLE of machine_multi

  withtype stack = instr list

  and machine_focus = {tactic: tactic, goal: Lf.class, stack: stack}
  and machine_multi = {multitactic: multitactic, state: state, stack: stack}
  and machine_retn = {state: state, stack: stack}
  and machine_throw = {exn: exn, goal: Lf.class, trace: stack, stack: stack} 

  datatype machine = 
     FOCUS of machine_focus
   | MULTI of machine_multi
   | RETN of machine_retn
   | THROW of machine_throw

  datatype 'a step = 
     STEP of 'a
   | FINAL of state
  
  fun init tac cl = 
    FOCUS {tactic = tac, goal = cl, stack = []}

  open Lf infix \ \\ `@ ==>

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
      Print.ctx Psi 
        ^ "\n   ===>  " 
        ^ Print.ntm evd

    val instr = 
      fn PUSH mtac => "{" ^ multitactic mtac ^ "}"
       | MTAC (x, mtac, st) => "mtac[" ^ Sym.toString x ^ "]{" ^ multitactic mtac ^ "}"
       | PREPEND Psi => "prepend{" ^ Print.ctx Psi ^ "}"
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

  fun stepFocus {tactic, goal, stack} : machine = 
    case tactic of 
       RULE rl => 
         (RETN {state = rule rl goal, stack = stack}
          handle exn => THROW {exn = exn, goal = goal, trace = [], stack = stack})
     | MT mtac =>
       let
         val x = Sym.new ()
       in
         RETN {state = [(x, goal)] \ eta (x, goal), stack = PUSH mtac :: stack}
       end

  fun stepRetn {state as Psi \ evd, stack} : machine step = 
    case stack of 
       PUSH mtac :: stk => STEP (MULTI {multitactic = mtac, state = state, stack = stk})
     | MTAC (x, mtac, Psi' \ evd') :: stk =>
       let
         val rhox = Sym.Env.singleton x evd
         val Psi'' = SubstN.ctx rhox Psi'
         val evd'' = SubstN.ntm rhox evd'
       in
         STEP (MULTI {multitactic = mtac, state = Psi'' \ evd'', stack = PREPEND Psi :: stk})
       end
     | PREPEND Psi' :: stk => STEP (RETN {state = Psi' @ Psi \ evd, stack = stk})
     | HANDLE _ :: stk => STEP (RETN {state = state, stack = stk})
     | [] => FINAL state

  fun stepThrow {exn, goal, trace, stack} : machine step =
    case stack of 
       [] => raise Exn.Refine (exn, goal, trace)
     | HANDLE multi :: stk => STEP (MULTI multi)
     | instr :: stk => STEP (THROW {exn = exn, goal = goal, trace = instr :: trace, stack = stk})

  fun stepMulti (multi as {multitactic, state as Psi \ evd, stack}) : machine =
    case (Psi, multitactic) of 
       (_, DEBUG msg) =>
       let
         val debugStr = 
           "[DEBUG] " ^ msg ^ "\n\n"
             ^ "Proof state: \n------------------------------\n"
             ^ Print.state state
             ^ "\n\nRemaining tasks: \n------------------------------\n"
             ^ Print.stack stack
             ^ "\n\n"
       in 
         print debugStr;
         RETN {state = state, stack = stack}
       end
     | (_, SEQ (mtac1, mtac2)) =>
       MULTI {multitactic = mtac1, state = state, stack = PUSH mtac2 :: stack}
     | ([], _) =>
       RETN {state = state, stack = stack}
     | ((x, cl) :: Psi, ALL tac) =>
       FOCUS {tactic = tac, goal = cl, stack = MTAC (x, ALL tac, Psi \ evd) :: stack}
     | (_, EACH []) =>
       RETN {state = state, stack = stack}
     | ((x, cl) :: Psi, EACH (tac :: tacs)) =>
       FOCUS {tactic = tac, goal = cl, stack = MTAC (x, EACH tacs, Psi \ evd) :: stack}
     | (_, ORELSE (mtac1, mtac2)) => 
       MULTI {multitactic = mtac1, state = state, stack = HANDLE multi :: stack}

  val step : machine -> machine step = 
    fn FOCUS foc => STEP (stepFocus foc)
     | MULTI multi => STEP (stepMulti multi)
     | THROW throw => stepThrow throw
     | RETN retn => stepRetn retn

  fun eval m = 
    case step m of 
       STEP m => eval m
     | FINAL st => st
end