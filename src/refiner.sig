signature LF_RULES = 
sig
  structure Lf : LF_TYPING

  type rule
  type state = (Lf.var * Lf.class, Lf.ntm) Lf.binder

  val rule : rule -> Lf.class -> state
  val printRule : rule -> string
end

signature LF_REFINER = 
sig
  structure Rules : LF_RULES

  datatype tactic =
     RULE of Rules.rule
   | ID
   | SEQ of tactic * multitactic

  and multitactic = 
     ALL of tactic
   | EACH of tactic list
   | DEBUG of string

  type machine
  val init : tactic -> Rules.Lf.class -> machine
  val eval : machine -> Rules.state
end

functor LfRefiner (R : LF_RULES) : LF_REFINER = 
struct
  structure Rules = R
  open R

  exception todo fun ?e = raise e

  datatype tactic =
     RULE of rule
   | ID
   | SEQ of tactic * multitactic

  and multitactic = 
     ALL of tactic
   | EACH of tactic list
   | DEBUG of string

  fun printTactic tac = 
    case tac of 
       RULE rl => printRule rl
     | ID => "id"
     | SEQ (tac, mtac) => printTactic tac ^ "; " ^ printMultitactic mtac
  
  and printMultitactic mtac = 
    case mtac of 
       ALL tac => printTactic tac
     | EACH tacs => "[" ^ printTactics tacs ^ "]"
     | DEBUG msg => "debug(\"" ^ msg ^ "\")"

  and printTactics tacs = 
    case tacs of 
       [] => ""
     | [tac] => printTactic tac 
     | tac :: tacs => printTactic tac ^ ", " ^ printTactics tacs


  datatype instr = 
     PUSH of multitactic
   | MTAC of Lf.var * multitactic * state
   | PREPEND of Lf.ctx

  type stack = instr list

  type machine_focus = tactic * Lf.class * stack
  type machine_multi = multitactic * state * stack
  type machine_retn = state * stack

  datatype machine = 
     FOCUS of machine_focus
   | MULTI of machine_multi
   | RETN of machine_retn

  datatype 'a step = 
     STEP of 'a
   | FINAL of state
  
  fun init tac cl = 
    FOCUS (tac, cl, [])

  open Lf infix \ \\ `@ ==>
  
  fun printState (Psi \ evd) = 
    Print.ctx Psi 
      ^ "\n   ===>  " 
      ^ Print.ntm evd

  val printInstr = 
    fn PUSH mtac => "{" ^ printMultitactic mtac ^ "}"
     | MTAC (x, mtac, st) => "mtac[" ^ Sym.toString x ^ "]({" ^ printMultitactic mtac ^ "}, " ^ printState st ^ ")"
     | PREPEND Psi => "prepend{" ^ Print.ctx Psi ^ "}"

  fun printStack stk = 
    case stk of 
       [] => "[]"
     | instr :: stk => printInstr instr ^ " :: " ^ printStack stk


  fun stepFocus (tac, cl, stk) : machine = 
    case tac of 
       RULE rl => RETN (rule rl cl, stk)
     | ID =>
       let
         val x = Sym.new ()
       in
         RETN ([(x, cl)] \ eta (x, cl), stk)
       end
     | SEQ (tac, mtac) => FOCUS (tac, cl, PUSH mtac :: stk)

  fun stepRetn (st as Psi \ evd, stk) : machine step = 
    case stk of 
       PUSH mtac :: stk => STEP (MULTI (mtac, st, stk))
     | MTAC (x, mtac, Psi' \ evd') :: stk =>
       let
         val rhox = Sym.Env.singleton x evd
         val Psi'' = SubstN.ctx rhox Psi'
         val evd'' = SubstN.ntm rhox evd'
       in
         STEP (MULTI (mtac, Psi'' \ evd'', PREPEND Psi :: stk))
       end
     | PREPEND Psi' :: stk => STEP (RETN (Psi' @ Psi \ evd, stk))
     | [] => FINAL st
       
  fun stepMulti (mtac, st as Psi \ evd, stk) : machine =
    case (Psi, mtac) of 
       (_, DEBUG msg) =>
       let
         val debugStr = 
           "[DEBUG] " ^ msg ^ "\n\n"
             ^ "Proof state: \n------------------------------\n"
             ^ printState st
             ^ "\n\nRemaining tasks: \n------------------------------\n"
             ^ printStack stk
             ^ "\n\n"
       in 
         print debugStr;
         RETN (st, stk)
       end
     | ([], _) => RETN (st, stk)
     | ((x, cl) :: Psi, ALL tac) => FOCUS (tac, cl, MTAC (x, ALL tac, Psi \ evd) :: stk)
     | (_, EACH []) => RETN (st, stk)
     | ((x, cl) :: Psi, EACH (tac :: tacs)) => FOCUS (tac, cl, MTAC (x, EACH tacs, Psi \ evd) :: stk)

  val step : machine -> machine step = 
    fn FOCUS foc => STEP (stepFocus foc)
     | MULTI multi => STEP (stepMulti multi)
     | RETN retn => stepRetn retn

  fun eval m = 
    case step m of 
       STEP m => eval m
     | FINAL st => st
end