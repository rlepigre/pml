module ListMap =
  struct
    type key = string

    type 'a t = (key * 'a) list

    let empty = []
    let singleton k v = [(k, v)]
    let add k v l = l @ [(k, v)]

    let mem = List.mem_assoc
    let find = List.assoc
    let is_empty = fun l -> l = empty

    let map  f l = List.map (fun (k, v) -> (k, f v)) l
    let mapi f l = List.map (fun (k, v) -> (k, f k v)) l

    let keys l = List.map fst l

    let bindings l = l

    let sort f l = List.sort (fun (_, d1) (_, d2) -> f d1 d2) l

    let fold f l acc = List.fold_left (fun acc (k, v) -> f k v acc) acc l

    let length = List.length

    let fold2 f acc l = List.fold_left2
            (fun acc (_, v) (_, v') -> f acc v v') acc l

    let hash f l =
      let mix x y = ((y lsl 17) - x) lxor ((x lsr 7) - y) in
      let mix3 x y z = mix x (mix y z) in
      List.fold_left (fun acc (k, v) -> mix3 (Hashtbl.hash k) (f v) acc) 17 l

    let fold_map f l acc =
      let acc = ref acc in
      let l = List.map (fun (s,x) -> let (x,a) = f s x !acc in
                                     acc := a; (s, x)) l in
      (l, !acc)

    let iter f l = List.iter (fun (k, v) -> f k v) l

    let equal cmp l1 l2 =
      let kcmp (k1,_) (k2,_) = String.compare k1 k2 in
      let vcmp (_,v1) (_,v2) = cmp v1 v2 in
      let len = List.length l1 in
      if len <> List.length l2 then false else
      let k1 = List.sort_uniq kcmp l1 in
      let k2 = List.sort_uniq kcmp l2 in
      if List.length k1 <> len then false else
      if List.length k2 <> len then false else
      if List.map fst k1 <> List.map fst k2 then false else
      List.for_all2 vcmp k1 k2

    let compare cmp l1 l2 =
      let kcmp (k1,_) (k2,_) = String.compare k1 k2 in
      let k1 = List.sort_uniq kcmp l1 in
      let k2 = List.sort_uniq kcmp l2 in
      let rec fn l1 l2 = match l1, l2 with
        | ([], []) ->  0
        | ([], _ ) -> -1
        | (_ , []) ->  1
        | ((k1,v1)::l1, (k2,v2)::l2) ->
           match String.compare k1 k2 with
           | 0 ->
              begin
                match cmp v1 v2 with
                | 0 -> fn l1 l2
                | c -> c
              end
           | c -> c
      in
      fn k1 k2

    let for_all f l = List.for_all (fun (k,v) -> f k v) l

    let exists f l = List.exists (fun (k,v) -> f k v) l
  end

include ListMap

open Bindlib

include Lift(ListMap)

let map_box : ('b -> 'a box) -> 'b t -> 'a t box =
  fun f m -> lift_box (map f m)
