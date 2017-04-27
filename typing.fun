functor LfTyping (Syn : LF_SYNTAX) : LF_TYPING = 
struct
  open Syn
  infix `@ \ \\

  structure LfExn = 
  struct
    datatype error = 
       EXPECTED_TYPE of {expected : rclass, actual : rclass}
     | MISSING_VARIABLE of {var : var, ctx : ctx}
     | SPINE_MISMATCH of {spine : spine, ctx : ctx}

    exception LfExn of error

    val description = 
      fn EXPECTED_TYPE {expected, actual} =>
           "Got type [" ^ Print.rclass actual ^ "] but it should have been [" ^ Print.rclass expected ^ "]."
       | MISSING_VARIABLE {var, ctx} => 
           "Could not find variable [" ^ Print.var var ^ "] in context [" ^ Print.ctx ctx ^ "]."
       | SPINE_MISMATCH {spine, ctx} => 
           "The spine [" ^ Print.spine spine ^ "] could not be checked about a context of incorrect length, [" ^ Print.ctx ctx ^ "]."
  end

  datatype judgment = 
     OK_CLASS of ctx * class
   | CHK of ctx * ntm * class
   | INF of ctx * rtm
   | CHK_SP of ctx * spine * ctx
   | CTX of ctx * ctx
   | EQ of rclass * rclass
   | ERR of LfExn.error
   | RET of rclass


  type metavar = var
  type frame = metavar * judgment
  type stack = frame list

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

  val step : stack -> stack = 
    fn (x, OK_CLASS (Gamma, cl)) :: stk => 
       let
         val Psi \ rcl = Unbind.class cl
         val x1 = Sym.new ()
         val x2 = Sym.new ()
         val x3 = Sym.new ()
       in
         case rcl of 
            `r => (x1, CTX (Gamma, Psi)) :: (x2, INF (Gamma @ Psi, r)) :: (x3, EQ (` (x2 `@ []), TYPE)) :: stk
          | TYPE => (x1, CTX (Gamma, Psi)) :: stk
       end
     | (x, CHK (Gamma, n, cl)) :: stk =>
       let
         val Psi \ rcl = Unbind.class cl
         val xs \ r = Unbind.ntm n
         val (rho, Psi') = Ren.rebindCtx xs Psi
         val rcl' = Ren.rclass rho rcl
         val y1 = Sym.new ()
         val y2 = Sym.new ()
       in
         (y1, INF (Gamma @ Psi', r)) :: (y2, EQ (rcl', `(y1 `@ []))) :: stk
       end
     | (x, CHK_SP (Gamma, sp, Psi)) :: stk => 
        let
          val (stk', _) = 
            ListPair.foldr
              (fn (n, (x,cl), (stk,rho)) =>
                 let
                   val cl' = SubstN.class rho cl
                   val rho' = Sym.Env.insert rho x n
                 in
                   ((Sym.new (), CHK (Gamma, n, cl')) :: stk, rho')
                 end)
              (stk, Sym.Env.empty)
              (sp, Psi)
        in
          stk'
        end
     | (x, INF (Gamma, y `@ sp)) :: stk =>
       (case findVar Gamma y of 
           SOME cl =>
           let
             val Psi \ rcl = Unbind.class cl
             val rcl' = SubstN.rclass (SubstN.zipSpine (List.map #1 Psi, sp)) rcl
             val x' = Sym.new ()
           in
             (x', CHK_SP (Gamma, sp, Psi)) :: (x, RET rcl') :: stk
           end
         | NONE => (Sym.new (), ERR (LfExn.MISSING_VARIABLE {var = x, ctx = Gamma})) :: stk)
     | (x, CTX (Gamma, Psi)) :: stk =>
       (case ListUtil.unsnoc Psi of 
           NONE => stk
         | SOME (Psi', (x, cl)) => 
           let
             val y1 = Sym.new ()
             val y2 = Sym.new ()
           in
             (y1, CTX (Gamma, Psi')) :: (y2, OK_CLASS (Gamma @ Psi', cl)) :: stk
           end)
     | (x, EQ (rcl1, rcl2)) :: stk =>
       if Eq.rclass (rcl1, rcl2) then 
         stk 
       else 
         (Sym.new (), ERR (LfExn.EXPECTED_TYPE {expected = rcl2, actual = rcl1})) :: stk
     | stk as [(_, RET rcl)] => stk
     | (x, RET rcl) :: stk =>
       let
         val rho = Sym.Env.insert Sym.Env.empty x ([] \ rcl)
       in
         List.map (fn (y, jdg) => (y, substJudgment rho jdg)) stk
       end
     | stk as (_, ERR _) :: _ => stk
     | [] => []

  val isFinal = 
    fn [] => true 
     | (_, RET _) :: [] => true
     | (_, ERR _) :: _ => true
     | _ => false


  fun eval stk = 
    if isFinal stk then 
      stk
    else
      eval (step stk)


  fun okCl Gamma cl = 
    case eval ([(Sym.new (), OK_CLASS (Gamma, cl))]) of 
       (_, ERR err) :: _ => raise LfExn.LfExn err
     | _ => ()

  fun ctx Gamma Psi = 
    case eval ([(Sym.new (), CTX (Gamma, Psi))]) of 
       (_, ERR err) :: _ => raise LfExn.LfExn err
     | _ => ()

  fun chk Gamma n cl = 
    case eval ([(Sym.new (), CHK (Gamma, n, cl))]) of 
       (_, ERR err) :: _ => raise LfExn.LfExn err
     | _ => ()

  fun chkSp Gamma sp Psi = 
    case eval ([(Sym.new (), CHK_SP (Gamma, sp, Psi))]) of 
       (_, ERR err) :: _ => raise LfExn.LfExn err
     | _ => ()
  
  fun inf Gamma r = 
    case eval ([(Sym.new (), INF (Gamma, r))]) of 
       (_, ERR err) :: _ => raise LfExn.LfExn err
     | [(_, RET rcl)] => rcl
     | _ => raise Fail "Internal error"

  structure LfExn = LfExnUtil (LfExn)
end