let map_opt : ('a -> 'b) -> 'a option -> 'b option = fun f o ->
  match o with None -> None | Some e -> Some (f e)

let from_opt : 'a option -> 'a -> 'a = fun o d ->
  match o with None -> d | Some e -> e

let from_opt' : 'a option -> (unit -> 'a) -> 'a = fun o f ->
  match o with None -> f () | Some e -> e

let map_snd : ('a -> 'b) -> ('c * 'a) list -> ('c * 'b) list = fun f l ->
  List.map (fun (k, v) -> (k, f v)) l

module M = Map.Make(String)



module IntOrd =
  struct
    type t = int
    let compare = compare
  end
module IntSet = Set.Make(IntOrd)
module IntMap = Map.Make(IntOrd)

module SetOrd =
  struct
    type t = IntSet.t
    let compare = IntSet.compare
  end
module SetMap = Map.Make(SetOrd)


