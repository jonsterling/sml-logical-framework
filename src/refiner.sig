signature LF_RULES = 
sig
  structure Lf : LF_TYPING

  type rule
  type goal = (Lf.var * Lf.class, Lf.rclass) Lf.bind
  type state = (Lf.var * goal, Lf.ntm) Lf.bind
  type names = unit -> Lf.var

  val rule : names -> rule -> goal -> state
  val printRule : rule -> string
end

signature LF_REFINER = 
sig
  structure Rules : LF_RULES

  (* This somewhat nonstandard arrangement of tactics and 
     multitactics is specifically to support local names for hypotheses
     in tactic scripts in the future. Trust Jon Sterling Thought! *)
  datatype tactic =
     RULE of Rules.rule
   | MT of multitactic

  and multitactic = 
     ALL of tactic
   | EACH of tactic list
   | DEBUG of string
   | BIND of Rules.Lf.var list * multitactic
   | SEQ of multitactic * multitactic
   | ORELSE of multitactic * multitactic

  structure Exn :
  sig
    type refine_error
    exception Refine of refine_error
    val description : refine_error -> string 
  end

  type machine
  val init : tactic -> Rules.goal -> machine
  val eval : machine -> Rules.state
end