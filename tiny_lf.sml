
functor TinyLf (Syn : LF_SYNTAX) : TINY_LF = 
struct
  open Syn
  infix `@ \\

  fun findVar Gamma (x : var) = 
    let
      fun go [] = NONE 
        | go ((y, cl) :: Gamma') = if Sym.eq (x, y) then SOME cl else go Gamma' 
    in
      go (List.rev Gamma)
    end

  fun ensure b msg = 
    if b then 
      ()
    else
      raise Fail msg

  fun okCl Gamma (PI (Psi, rcl)) =
    let
      val _ = ctx Gamma Psi
    in
      case rcl of 
         ` r => ensure (Eq.rclass (inf (Gamma @ Psi) r, TYPE)) "Expected TYPE"
       | TYPE => ()
    end

  and chk Gamma (xs \\ r) (PI (Psi, rcl)) =
    let
      val (rho, Psi') = Ren.rebindCtx xs Psi
      val rcl' = Ren.rclass rho rcl
    in
      ensure (Eq.rclass (inf (Gamma @ Psi') r, rcl')) "Error checking lambda"
    end

  and inf Gamma (x `@ sp) : rclass =
    case findVar Gamma x of 
       SOME (PI (Psi, rcl)) =>
         (chkSp Gamma sp Psi;
          Subst.rclass (Subst.zipSpine (List.map #1 Psi, sp)) rcl)
     | NONE => raise Fail ("Could not find variable " ^ Sym.toString x)

  and chkSp Gamma (sp : spine) Psi : unit =
    case (sp, Psi) of
       ([], []) => ()
     | (n :: sp', (x, cl) :: Psi') =>
         let
           val rho = Subst.zipSpine (List.map #1 Psi', sp')
         in
           chk Gamma n (Subst.class rho cl);
           chkSp Gamma sp' Psi'
         end
     | _ => raise Fail ("chkSp length mismatch: " ^ Print.spine sp ^ " / " ^ Print.ctx Psi)

  and ctx Gamma Psi = 
    case ListUtil.unsnoc Psi of 
       NONE => ()
     | SOME (Psi', (x, cl)) => 
       (ctx Gamma Psi';
        okCl (Gamma @ Psi') cl)
end