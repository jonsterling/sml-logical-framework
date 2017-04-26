functor TinyLf (Syn : LF_SYNTAX) : TINY_LF = 
struct
  open Syn
  infix `@ \

  structure Exn = 
  struct
    datatype error = 
       EXPECTED_TYPE of {rtm : rtm, expected : rclass, actual : rclass}
     | MISSING_VARIABLE of {var : var, ctx : ctx}
     | SPINE_MISMATCH of {spine : spine, ctx : ctx}

    exception LfExn of error

    val description = 
      fn EXPECTED_TYPE {rtm, expected, actual} =>
           "The classifier of [" ^ Print.rtm rtm ^ "] was [" ^ Print.rclass actual ^ "] but it should have been [" ^ Print.rclass expected ^ "]."
       | MISSING_VARIABLE {var, ctx} => 
           "Could not find variable [" ^ Sym.toString var ^ "] in context [" ^ Print.ctx ctx ^ "]."
       | SPINE_MISMATCH {spine, ctx} => 
           "The spine [" ^ Print.spine spine ^ "] could not be checked about a context of incorrect length, [" ^ Print.ctx ctx ^ "]."

    fun debug e = 
      e ()
      handle LfExn err => 
        (print ("\n" ^ description err ^ "\n");
         raise LfExn err)
  end

  fun findVar Gamma x = 
    let
      fun go [] = NONE 
        | go ((y, cl) :: Gamma') = if Sym.eq (x, y) then SOME cl else go Gamma' 
    in
      go (List.rev Gamma)
    end

  fun ensure (b, err) = 
    if b then 
      ()
    else
      raise Exn.LfExn err

  fun okCl Gamma (PI (Psi, rcl)) =
    let
      val _ = ctx Gamma Psi
    in
      case rcl of 
         ` r => 
           let
             val rcl = inf (Gamma @ Psi) r
           in
             ensure (Eq.rclass (rcl, TYPE), Exn.EXPECTED_TYPE {rtm = r, expected = TYPE, actual = rcl})
           end
       | TYPE => ()
    end

  and chk Gamma n (PI (Psi, rcl)) =
    let
      val xs \ r = Unbind.ntm n
      val (rho, Psi') = Ren.rebindCtx xs Psi
      val rcl' = Ren.rclass rho rcl
      val rcl'' = inf (Gamma @ Psi') r
    in
      ensure (Eq.rclass (rcl', rcl''), Exn.EXPECTED_TYPE {rtm = r, expected = rcl', actual = rcl''})
    end

  and inf Gamma (x `@ sp) =
    case findVar Gamma x of 
       SOME (PI (Psi, rcl)) =>
         (chkSp Gamma sp Psi;
          Subst.rclass (Subst.zipSpine (List.map #1 Psi, sp)) rcl)
     | NONE => raise Exn.LfExn (Exn.MISSING_VARIABLE {var = x, ctx = Gamma})

  and chkSp Gamma =
    let 
      exception LengthMismatch
      val rec go = 
        fn ([], []) => ()
         | (n :: sp, (x, cl) :: Psi) => 
           let
             val rho = Subst.zipSpine (List.map #1 Psi, sp)
           in
             chk Gamma n (Subst.class rho cl);
             go (sp, Psi)
           end
        | _ => raise LengthMismatch
    in
      fn sp => fn Psi => 
        go (sp, Psi)
        handle LengthMismatch => 
          raise Exn.LfExn (Exn.SPINE_MISMATCH {spine = sp, ctx = Psi})
    end

  and ctx Gamma Psi = 
    case ListUtil.unsnoc Psi of 
       NONE => ()
     | SOME (Psi', (x, cl)) => 
       (ctx Gamma Psi';
        okCl (Gamma @ Psi') cl)
end