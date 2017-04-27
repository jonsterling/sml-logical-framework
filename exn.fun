functor LfExnUtil (Exn : LF_EXN) : LF_EXN_UTIL = 
struct
  open Exn
  fun debug e = 
    e ()
    handle LfExn err => 
       (print ("\n" ^ description err ^ "\n");
        raise LfExn err)
     | exn => 
       (print ("\n" ^ exnMessage exn ^ "\n");
       raise exn)
end