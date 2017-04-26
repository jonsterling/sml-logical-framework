  signature LF_EXN =
  sig
    type error
    exception LfExn of error
    val description : error -> string
    val debug : (unit -> 'a) -> 'a
  end