(** Small timer library for timing the application of functions. *)

let unix_time : unit -> float = fun () ->
  Unix.(let t = times () in t.tms_utime +. t.tms_stime)

let time : (float -> unit) -> ('a -> 'b) -> 'a -> 'b = fun rt fn x ->
  let t = unix_time () in
  try let res = fn x in rt (unix_time () -. t); res
  with e -> rt (unix_time () -. t); raise e

type t = { name : string
         ; mutable start : float
         ; mutable time  : float
         ; mutable cumul : float
         ; mutable count : int }
type chrono = t

let get_name  : t -> string = fun p -> p.name
let get_time  : t -> float  = fun p -> p.time
let get_cumul : t -> float  = fun p -> p.cumul
let get_count : t -> int    = fun p -> p.count

let all_chronos : t list ref = ref []

let create name =
  let chr = { name ; time = 0.0 ; cumul = 0.0; start = 0.0; count = 0 } in
  all_chronos := chr :: !all_chronos; chr

let root_chrono = create "others"

let current = ref root_chrono

(** Invariant: p.start is meaningful when !current = p *)
let add_time chr f x =
  chr.count <- chr.count + 1;
  if chr == !current then f x else
  let st = unix_time () in
  let previous = !current in
  previous.time <- previous.time +. st -. previous.start;
  chr.start <- st;
  current := chr;
  try
    let r = f x in
    assert (chr == !current);
    let ut = unix_time () in
    chr.time  <- chr.time  +. ut -. chr.start;
    chr.cumul <- chr.cumul +. ut -. st;
    previous.start <- ut;
    current := previous;
    r
  with e ->
    assert (chr == !current);
    let ut = unix_time () in
    chr.time  <- chr.time  +. ut -. chr.start;
    chr.cumul <- chr.cumul +. ut -. st;
    previous.start <- ut;
    current := previous;
    raise e

let iter fn =
  let gn st = fn st.name st.time st.cumul st.count in
  List.iter gn !all_chronos
