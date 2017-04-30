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
   | SEQ of multitactic * multitactic

  type machine
  val init : tactic -> Rules.Lf.class -> machine
  val eval : machine -> Rules.state
end