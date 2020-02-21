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
(** [eq_closure] is an alternative to the polymorphic equality function [(=)],
    that compares closures using [(==)] instead of failing. Note that equality
    testing is consequently not perfect. *)
let eq_closure : type a. a -> a -> bool = fun v1 v2 ->
  (* We remember encountered values in [eq_done] to handle cyclicity. *)
  let eq_done : (Obj.t * Obj.t) list ref = ref [] in
  let rec eq : Obj.t -> Obj.t -> bool = fun v1 v2 ->
    (* Physical equality is tested first. *)
    v1 == v2 ||
    (* We then look at tags, and unfold potential forward blocks. *)
    let t1 = Obj.tag v1 in
    if t1 = Obj.forward_tag then eq (Obj.field v1 0) v2 else
    let t2 = Obj.tag v2 in
    if t2 = Obj.forward_tag then eq v1 (Obj.field v2 0) else
    (* Tags must otherwise be the same to have equality. *)
    t1 == t2 &&
    (* Strings, doubles and arrays of doubles are compared using [=]. *)
    if t1 = Obj.string_tag then v1 = v2 else
    if t1 = Obj.double_tag then v1 = v2 else
    if t1 = Obj.double_array_tag then v1 = v2 else
    (* For everything that is not a non-constant constructors, equality failed
    at this point (e.g., for closures or sealed values).  Such values are only
    considered equal if physical equality succeeds (it was tested already). *)
    Obj.first_non_constant_constructor_tag <= t1 &&
    t1 <= Obj.last_non_constant_constructor_tag &&
    Obj.size v1 == Obj.size v2 && (* Number of fields should be equal. *)
    (* We recursively explore the fields. *)
    let rec fn = function
      | (v1', v2')::l ->
         begin
           match (v1 == v1', v2 == v2') with
           | (true , true ) -> true
           | (true , false) -> false
           | (false, true ) -> false
           | (_    , _    ) -> fn l
         end
      | []            ->
         let rec gn i =
           i < 0 || (eq (Obj.field v1 i) (Obj.field v2 i) && gn (i-1))
         in
         eq_done := (v1, v2) :: !eq_done; gn (Obj.size v1 - 1)
    in
    fn !eq_done
  in
  eq (Obj.repr v1) (Obj.repr v2)


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
        if eq_closure k key then (h.size <- h.size - 1; next)
        else Cons(k, i, remove_bucket next)
  in
  let i = key_index h key in
  h.data.(i) <- remove_bucket h.data.(i)

let rec find_rec key = function
  | Nil              -> raise Not_found
  | Cons(k, d, rest) -> if eq_closure key k then d else find_rec key rest

let find h key =
  match h.data.(key_index h key) with
  | Nil                 -> raise Not_found
  | Cons(k1, d1, rest1) ->
      if eq_closure key k1 then d1 else
      match rest1 with
      | Nil                 -> raise Not_found
      | Cons(k2, d2, rest2) ->
          if eq_closure key k2 then d2 else
          match rest2 with
          | Nil                 -> raise Not_found
          | Cons(k3, d3, rest3) ->
              if eq_closure key k3 then d3 else find_rec key rest3

let find_all h key =
  let rec find_in_bucket = function
    | Nil              -> []
    | Cons(k, d, rest) -> if eq_closure k key then d :: find_in_bucket rest
                          else find_in_bucket rest
  in find_in_bucket h.data.(key_index h key)

let replace h key info =
  let rec replace_bucket = function
    | Nil              -> raise Not_found
    | Cons(k, i, next) -> if eq_closure k key then Cons(key, info, next)
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
  | Cons(k, _, rest) -> eq_closure k key || mem_in_bucket rest
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
