  signature LF_EXN =
  sig
    type error
    exception LfExn of error
    val description : error -> string
  end

  signature LF_EXN_UTIL = 
  sig
    include LF_EXN
    val debug : (unit -> 'a) -> 'a
  end