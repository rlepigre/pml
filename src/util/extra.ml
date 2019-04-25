module List =
  struct
    include List

    let rec find_first : ('a -> bool) -> 'a list -> 'a option =
      fun pred l ->
        match l with
        | []   -> None
        | x::l -> if pred x then Some x else find_first pred l
  end

module Array = struct
  include Array

  let for_all2 f a1 a2 =
    try
      Array.iter2 (fun x y -> if not (f x y) then raise Exit) a1 a2;
      true
    with Exit -> false

  let fold_left2 f acc a1 a2 =
    let acc = ref acc in
    Array.iter2 (fun x y -> acc := f !acc x y) a1 a2;
    !acc

end

module Option =
  struct
    type 'a t = 'a option

    let none : type a. a option =
      None

    let some : type a. a -> a option =
      fun x -> Some(x)

    let default : type a. a -> a option -> a =
      fun d xo ->
        match xo with
        | None    -> d
        | Some(x) -> x

    let udefault : type a. (unit -> a) -> a option -> a =
      fun d xo ->
        match xo with
        | None    -> d ()
        | Some(x) -> x

    let map : type a b. (a -> b) -> a option -> b option =
      fun f xo ->
        match xo with
        | None    -> None
        | Some(x) -> Some(f x)

    let default_map : type a b. b -> (a -> b) -> a option -> b =
      fun d f xo ->
        match xo with
        | None    -> d
        | Some(x) -> f x

    let udefault_map : type a b. (unit -> b) -> (a -> b) -> a option -> b =
      fun d f xo ->
        match xo with
        | None    -> d ()
        | Some(x) -> f x

    let fold : type a b. (b -> a -> a) -> b option -> a -> a =
      fun f xo a ->
        match xo with
        | None -> a
        | Some b -> f b a

    let iter : type a. (a -> unit) -> a option -> unit =
      fun f xo ->
        match xo with
        | None    -> ()
        | Some(x) -> f x

    let equal : type a. (a -> a -> bool) -> a option -> a option -> bool =
      fun cmp ao bo ->
        match (ao, bo) with
        | (None  , None  ) -> true
        | (Some a, Some b) -> cmp a b
        | (_     , _     ) -> false

    let compare : type a. (a -> a -> int) -> a option -> a option -> int =
      fun cmp ao bo ->
        match (ao, bo) with
        | (None   , None   ) -> 0
        | (None   , Some(_)) -> -1
        | (Some(_), None   ) -> 1
        | (Some(a), Some(b)) -> cmp a b
  end
