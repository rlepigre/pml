
module type Time = sig
  type t
  val save : unit -> t
  val rollback : t -> unit
  type futur
  val save_futur : t -> futur
  val return_futur : futur -> t
end

module NoTime : Time = struct
  type t = unit
  let save () = ()
  let rollback () = ()
  type futur = unit
  let save_futur () = ()
  let return_futur () = ()
end

module Make(T:Time) = struct

  module Time =
    struct
      (** time is a list containing the undo to go back to the time before
          and the next time in the future. List are from past to future, hence
          if the a past time is not accessible, it is collocted by the GC.

          Undone is not a valid time, it can appear only in the next field *)
      type u = Undone : u (** already undone change up to that time (excluded)
                              or before*)
             | Futur : { mutable next : u ; r : 'a ref; old : 'a } -> u


      (** time of this module and the inherited module together, for nested
         times *)
      type t = u * T.t

      (** reference holding the current time *)
      let current : u ref =
        ref (Futur{ next = Undone; r = ref (); old = () })

      (** save the time, both local and inherited *)
      let save : unit -> t = fun () -> (!current, T.save ())

      (** rollback to the given time *)
      let rollback : t -> unit = fun (t,ut) ->
        (** undo all time in the futur of t, and make t the current time. *)
        let rec fn = function
          | Undone -> ()
          | Futur ({ next; r; old } as t) ->
                       t.next <- Undone;
                       fn next; (* tail rec call would be incorrect if the
                                   same ref was updated twice *)
                       r:= old
        in
        T.rollback ut;
        current := t;
        match t with
        | Undone -> assert false
        | Futur ({ next; _ } as t) -> t.next <- Undone; fn next

      type bu = R : ('a ref * 'a) -> bu
      type futur = t * bu list * T.futur

      (* same as roll_back, but we will be able to return in the futur *)
      let save_futur : t -> futur =  fun (t,ut as t0) ->
        let sf = ref [] in
        (** undo all time in the futur of t, and make t the current time. *)
        let rec fn = function
          | Undone -> ()
          | Futur ({ next; r; old }) ->
                       sf := R (r, !r) :: !sf;
                       fn next
        in
        let bu = T.save_futur ut in
        begin
          match t with
          | Undone -> assert false
          | Futur ({ next; _ }) -> fn next
        end;
        (t0, List.rev !sf, bu)

      let (:=) : 'a ref -> 'a -> unit = fun r v ->
        let old = !r in
        let t = Futur { next = Undone; r; old } in
        (match !current with
         | Undone -> assert false
         | Futur u -> u.next <- t);
        current := t; r := v

      let return_futur : futur -> t = fun (t, sf, bu) ->
        let _ = T.return_futur bu in
        rollback t;
        let fn (R(ptr,v)) = ptr := v in
        List.iter fn sf;
        save ()

    end


  let (:=) = Time.(:=)

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
  module Time : Time
  val ( := ) : 'a ref -> 'a -> unit
  val incr : int ref -> unit
  val decr : int ref -> unit
  val apply : ('a -> 'b) -> 'a -> 'b
  val pure_apply : ('a -> 'b) -> 'a -> 'b
  val pure_test : ('a -> bool) -> 'a -> bool
  type 'a tref
  val tref : 'a -> 'a tref
  val get : Time.t -> 'a tref -> 'a
  val set : Time.t -> 'a tref -> 'a -> Time.t
end

include Make(NoTime)
