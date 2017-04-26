
functor TinyLf (Syn : LF_SYNTAX) : TINY_LF = 
struct
  open Syn
  infix `@ \\

  fun lookupVar rho x = 
    Sym.Env.lookup rho x
    handle _ => x

  fun envFromSpine (sp, xs) = 
    ListPair.foldr
      (fn (x, n, rho) => Sym.Env.insert rho x n)
      Sym.Env.empty
      (xs, List.rev sp)

  fun rebindCtx (xs, Psi) = 
    let
      fun go rho [] [] out = (rho, out)
        | go rho (x :: xs) ((y, cl) :: Psi) out =
            go (Sym.Env.insert rho y x) xs Psi ((x, renCl rho cl) :: out)
        | go _ _ _ _ = raise Fail "Incorrect length of contexts"
      val (rho', Psi') = go Sym.Env.empty xs Psi []
    in
      (rho', List.rev Psi')
    end

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
         ` r => ensure (eqRcl (inf (Gamma @ Psi) r, TYPE)) "Expected TYPE"
       | TYPE => ()
    end

  and chk Gamma (xs \\ r) (PI (Psi, rcl)) =
    let
      val (rho, Psi') = rebindCtx (xs, Psi)
      val rcl' = renRcl rho rcl
    in
      ensure (eqRcl (inf (Gamma @ Psi') r, rcl')) "Error checking lambda"
    end

  and inf Gamma (x `@ sp) : rclass =
    case findVar Gamma x of 
       SOME (PI (Psi, rcl)) =>
         (chkSp Gamma sp Psi;
          substRcl (envFromSpine (sp, List.map #1 Psi)) rcl)
     | NONE => raise Fail ("Could not find variable " ^ Sym.toString x)

  and chkSp Gamma (sp : spine) Psi : unit =
    case (sp, Psi) of
       ([], []) => ()
     | (n :: sp', (x, cl) :: Psi') =>
         let
           val rho = envFromSpine (sp', List.map #1 Psi')
         in
           chk Gamma n (substCl rho cl);
           chkSp Gamma sp' Psi'
         end
     | _ => raise Fail ("chkSp length mismatch: " ^ toStringSp sp ^ " / " ^ toStringCtx Psi)

  and ctx Gamma Psi = 
    case ListUtil.unsnoc Psi of 
       NONE => ()
     | SOME (Psi', (x, cl)) => 
       (ctx Gamma Psi';
        okCl (Gamma @ Psi') cl)

end