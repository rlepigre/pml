
module Val =
  struct
    type t = v ex

    let equal : t -> t -> bool =
      fun v1 v2 -> eq_expr (Pos.none v1) (Pos.none v2)

    let hash t = Hashtbl.hash t
  end

module HVal = Weak.Make(Val)

let hval : v ex -> v ex =
  let tbl = HVal.create 1001 in
  fun d -> d (*
    try HVal.find tbl d
    with Not_found -> HVal.add tbl d; d*)
