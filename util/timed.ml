module Time =
  struct
    type t = { mutable next : u ; undo : unit -> unit }

     and u = Current | Past of t | Invalid

    let current : t ref =
      ref { next = Current ; undo = (fun () -> ()) }

    let save : unit -> t = fun () -> !current

    exception Bad_time

    let rollback : t -> unit = fun t ->
      let rec fn = function
        | Current -> ()
        | Past  t -> fn t.next; t.undo (); t.next <- Invalid
        | Invalid -> raise Bad_time
      in fn t.next; t.next <- Current; current := t
  end

let (<<) : 'a ref -> 'a -> unit = (:=)

let (:=) : 'a ref -> 'a -> unit = fun r v ->
  let open Time in
  let v0 = !r in
  let t = { next = Current; undo = (fun () -> r := v0) } in
  !current.next <- Past t; current := t; r := v

let incr : int ref -> unit = fun r -> r := !r + 1
let decr : int ref -> unit = fun r -> r := !r - 1

let pure_apply : ('a -> 'b) -> 'a -> 'b = fun f v ->
  let t = Time.save () in
  try
    let r = f v in
    Time.rollback t; r
  with e ->
    Time.rollback t; raise e

let apply : ('a -> 'b) -> 'a -> 'b = fun f v ->
  let t = Time.save () in
  try
    f v
  with e ->
    Time.rollback t; raise e

let pure_test : ('a -> bool) -> 'a -> bool = fun f v ->
  let t = Time.save () in
  try
    let r = f v in
    if not r then Time.rollback t; r
  with e ->
    Time.rollback t; raise e

type 'a tref = 'a ref

let tref x = ref x

let get t r = Time.rollback t; !r

let set r v = r := v; Time.save ()
