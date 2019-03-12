open List

type ('a, 'b) t =
  { data : ('a * 'b list) list
  ; eq   : 'a -> 'a -> bool }

type ('a, 'b) buckets = ('a, 'b) t

let empty : ('a -> 'a -> bool) -> ('a, 'b) t = fun eq ->
  { data = [] ; eq }

let add : 'a -> 'b -> ('a, 'b) t -> ('a, 'b) t = fun key v bcks ->
  let rec find_and_add acc data =
    match data with
    | []                              -> (key, [v]) :: acc
    | (k,ls)::data when bcks.eq k key -> rev_append ((key, v::ls)::acc) data
    | c     ::data                    -> find_and_add (c::acc) data
  in
  { bcks with data = find_and_add [] bcks.data }

let find : 'a -> ('a, 'b) t -> 'b list = fun key bcks ->
  try snd (List.find (fun (x,_) ->  bcks.eq key x) bcks.data)
  with Not_found -> []

let length : ('a, 'b) t -> int = fun bcks -> List.length bcks.data
