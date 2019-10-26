(** Modified version of the [Hashbtl] library, to work with types containing
    functions. Physical equality is used when [Pervasives.compare] raises an
    exception. Note that this is only used when the hash function leads to a
    collision (and thus quite rarely). *)

type ('a, 'b) bucketlist = Nil | Cons of 'a * 'b * ('a, 'b) bucketlist

type ('a, 'b) t =
  { mutable size : int                       (* Number of entries.  *)
  ; mutable data : ('a, 'b) bucketlist array (* The buckets.        *)
  ; initial_size : int }                     (* Initial array size. *)

(* Full comparision function (compares closures with physical equality). *)
let compare x y =
  try compare x y = 0 with _ -> x == y

(* Creates a fresh, empty table. *)
let create initial_size =
  let rec power_2_above x n =
    if x >= n ||  x * 2 > Sys.max_array_length then x
    else power_2_above (x * 2) n
  in
  let initial_size = power_2_above 16 initial_size in
  let data = Array.make initial_size Nil in
  { initial_size ; size = 0 ; data }

(* Clear the table (without resizing the bucket array. *)
let clear h =
  h.size <- 0;
  for i = 0 to Array.length h.data - 1 do
    h.data.(i) <- Nil
  done

(* Reset the table to its initial state. *)
let reset h =
  let len = Array.length h.data in
  if Obj.size (Obj.repr h) < 4 || len = h.initial_size then clear h
  else (h.size <- 0; h.data <- Array.make h.initial_size Nil)

(* Copy the table. *)
let copy h = { h with data = Array.copy h.data }

(* Size of the table (number of bindings). *)
let length h = h.size

let resize indexfun h =
  let odata = h.data in
  let osize = Array.length odata in
  let nsize = osize * 2 in
  if nsize < Sys.max_array_length then begin
    let ndata = Array.make nsize Nil in
    h.data <- ndata;          (* so that indexfun sees the new bucket count *)
    let rec insert_bucket = function
      | Nil                   -> ()
      | Cons(key, data, rest) ->
          insert_bucket rest; (* preserve original order of elements *)
          let nidx = indexfun h key in
          ndata.(nidx) <- Cons(key, data, ndata.(nidx))
    in
    for i = 0 to osize - 1 do
      insert_bucket odata.(i)
    done
  end

let key_index h key =
  (Hashtbl.hash_param 10 100 key) land (Array.length h.data - 1)

let add h key info =
  let i = key_index h key in
  let bucket = Cons(key, info, h.data.(i)) in
  h.data.(i) <- bucket;
  h.size <- h.size + 1;
  if h.size > Array.length h.data lsl 1 then resize key_index h

let remove h key =
  let rec remove_bucket = function
    | Nil              -> Nil
    | Cons(k, i, next) ->
        if compare k key then (h.size <- h.size - 1; next)
        else Cons(k, i, remove_bucket next)
  in
  let i = key_index h key in
  h.data.(i) <- remove_bucket h.data.(i)

let rec find_rec key = function
  | Nil              -> raise Not_found
  | Cons(k, d, rest) -> if compare key k then d else find_rec key rest

let find h key =
  match h.data.(key_index h key) with
  | Nil                 -> raise Not_found
  | Cons(k1, d1, rest1) ->
      if compare key k1 then d1 else
      match rest1 with
      | Nil                 -> raise Not_found
      | Cons(k2, d2, rest2) ->
          if compare key k2 then d2 else
          match rest2 with
          | Nil                 -> raise Not_found
          | Cons(k3, d3, rest3) ->
              if compare key k3 then d3 else find_rec key rest3

let find_all h key =
  let rec find_in_bucket = function
    | Nil              -> []
    | Cons(k, d, rest) -> if compare k key then d :: find_in_bucket rest
                          else find_in_bucket rest
  in find_in_bucket h.data.(key_index h key)

let replace h key info =
  let rec replace_bucket = function
    | Nil              -> raise Not_found
    | Cons(k, i, next) -> if compare k key then Cons(key, info, next)
                          else Cons(k, i, replace_bucket next)
  in
  let i = key_index h key in
  let l = h.data.(i) in
  try  h.data.(i) <- replace_bucket l
  with Not_found ->
    h.data.(i) <- Cons(key, info, l);
    h.size <- h.size + 1;
    if h.size > Array.length h.data lsl 1 then resize key_index h

let mem h key =
  let rec mem_in_bucket = function
  | Nil              -> false
  | Cons(k, _, rest) -> compare k key || mem_in_bucket rest
  in mem_in_bucket h.data.(key_index h key)

let iter f h =
  let rec do_bucket = function
    | Nil              -> ()
    | Cons(k, d, rest) -> f k d; do_bucket rest
  in
  let d = h.data in
  for i = 0 to Array.length d - 1 do
    do_bucket d.(i)
  done

let fold f h init =
  let rec do_bucket b accu =
    match b with
    | Nil              -> accu
    | Cons(k, d, rest) -> do_bucket rest (f k d accu)
  in
  let d = h.data in
  let accu = ref init in
  for i = 0 to Array.length d - 1 do
    accu := do_bucket d.(i) !accu
  done; !accu
