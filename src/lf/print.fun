functor LfSyntaxPrint (Lf : LF_SYNTAX) : LF_SYNTAX_PRINT = 
struct
  open Lf
  infix 0 @@
  infix 1 \ \\ `@ --> ==>

  fun var x = 
    Sym.toString x

  fun vars xs =
    case xs of
        [] => ""
      | x :: [] => var x
      | x :: xs => var x ^ "," ^ vars xs

  fun pi (Psi \ rcl) =
    case Psi of
        [] => rclass rcl
      | _ => "{" ^ ctx Psi ^ "}" ^ rclass rcl

  and class cl = 
    pi (Unbind.class cl)

  and ctx Psi =
    case Psi of
        [] => "-"
      | (x, cl) :: [] => var x ^ ":" ^ class cl
      | (x, cl) :: Psi' => var x ^ ":" ^ class cl ^ ", " ^ ctx Psi'

  and rclass rcl =
    case rcl of
        `r => rtm r
      | TYPE => "*"

  and rtm (x `@ sp) =
    case sp of
        [] => var x
      | _ => var x ^ "[" ^ spine sp ^ "]"

  and spine sp =
    case sp of
        [] => "-"
      | n :: [] => ntm n
      | n :: sp => ntm n ^ "," ^ spine sp

  and lam (xs \ r) =
    case xs of
        [] => rtm r
      | _ =>  "[" ^ vars xs ^ "]" ^ rtm r

  and ntm n = 
    lam (Unbind.ntm n)
end