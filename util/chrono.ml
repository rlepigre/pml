(** Small timer library for timing the application of functions. *)

let unix_time : unit -> float = fun () ->
  Unix.(let t = times () in t.tms_utime +. t.tms_stime)

let time : (float -> unit) -> ('a -> 'b) -> 'a -> 'b = fun rt fn x ->
  let t = unix_time () in
  try let res = fn x in rt (unix_time () -. t); res
  with e -> rt (unix_time () -. t); raise e

type t_aux = { name : string ; time : float ; count : int }
type t = t_aux ref
type chrono = t

let get_name  : t -> string = fun p -> (!p).name
let get_time  : t -> float  = fun p -> (!p).time
let get_count : t -> int    = fun p -> (!p).count

let all_chronos : t list ref = ref []

let create name =
  let st = { name ; time = 0.0 ; count = 0 } in
  let chr = ref st in all_chronos := chr :: !all_chronos; chr

type state = t_aux list

let save_state () =
  let fn chr =
    let r = !chr in
    chr := { r with time = 0.0 ; count = 0 }; r
  in
  List.map fn !all_chronos

let restore_state backup =
  List.iter2 (:=) !all_chronos backup

let chrono_stack = ref 0.0

let pop_time t0 t1 =
  let t2 = unix_time () in
  let s = !chrono_stack in
  let d = t2 -. t1 +. t0 in
  chrono_stack := d; d -. s

let add_time p f x =
  let st = !p in
  let ut = unix_time () in
  p := { st with count = st.count + 1 };
  let ud0 = !chrono_stack in
  try
    let r = f x in
    let t = pop_time ud0 ut in
    let st = !p in
    p := { st with time = st.time +. t };
    r
  with e ->
    let t = pop_time ud0 ut in
    let st = !p in
    p := { st with time = st.time +. t };
    raise e

let iter fn =
  let gn { contents = st } = fn st.name st.time st.count in
  List.iter gn !all_chronos
