module StrMap = Map.Make(String)

include StrMap

open Bindlib

let lift_box : 'a bindbox t -> 'a t bindbox =
  fun m -> let module B = Lift(StrMap) in B.f m

let map_box : ('b -> 'a bindbox) -> 'b t -> 'a t bindbox =
  fun f m -> lift_box (map f m)
