structure ListUtil : LIST_UTIL = 
struct
  fun unsnoc xs = 
    let
      val n = List.length xs - 1
      val x = List.nth (xs, n)
      val xs' = List.take (xs, n)
    in
      SOME (xs', x)
    end
    handle General.Subscript => NONE
end
