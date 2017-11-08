
exception Bad_time


module type Time = sig
  type t
  val rollback : t -> unit
  val save : unit -> t
end

module NoTime : Time = struct
  type t = unit
  let rollback () = ()
  let save () = ()
end

module Make(T:Time) = struct

  module Time =
    struct
      type r = { mutable next : u ; undo : unit -> unit }

       and u = Current | Past of r | Invalid

      type t = r * T.t

      let current : r ref =
        ref { next = Current ; undo = (fun () -> ()) }

      let save : unit -> t = fun () -> (!current, T.save ())

      let rollback : t -> unit = fun (t,ut) ->
        let rec fn = function
          | Current -> ()
          | Past  t -> fn t.next; t.undo (); t.next <- Invalid
          | Invalid -> raise Bad_time
        in T.rollback ut; fn t.next; t.next <- Current; current := t;
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

  let set t r v = Time.rollback t; r := v; Time.save ()

end

module type Timed = sig
  module Time : sig
    type t
    val save : unit -> t
    val rollback : t -> unit
  end
  val ( << ) : 'a ref -> 'a -> unit
  val ( := ) : 'a ref -> 'a -> unit
  val incr : int ref -> unit
  val decr : int ref -> unit
  val apply : ('a -> 'b) -> 'a -> 'b
  val pure_apply : ('a -> 'b) -> 'a -> 'b
  val pure_test : ('a -> bool) -> 'a -> bool
  type 'a tref = 'a ref
  val tref : 'a -> 'a tref
  val get : Time.t -> 'a tref -> 'a
  val set : Time.t -> 'a tref -> 'a -> Time.t
end

include Make(NoTime)
