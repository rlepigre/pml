(** Timed references (with rollback). This module provides alternative
    functions for updating references (terms of type ['a ref]) and  it
    enables the restoration of a previously saved state  by  "undoing"
    the updates. *)

module Time :
(** [Time] submodule allows to [save] the current time and [rollback]
    the references. If the time is not accessible.

    old values are collected by the GC if no time are accessible
    that would allow to rollback to this value. *)
  sig
    (** Type representing a precise time in the program execution. *)
    type t

    (** Save the current execution time. *)
    val save : unit -> t

    exception Bad_time

    (** Rollback all the reference updates that were issued since the
        provided time. Raise the exception [Time.Bad_time] if you
        rollback to a time that was already undone. *)
    val rollback : t -> unit
  end

(** Usual reference update function, renamed due to the use of [(:=)]
    for its timed counterpart bellow. *)
val ( << ) : 'a ref -> 'a -> unit

(** This function can be used to update a reference, which recording
    the changes. This is done transparently, so this function can be
    used as the usual update function. *)
val ( := ) : 'a ref -> 'a -> unit

(** Incrementation function for a reference of type [int]. The update
    is again transparently recorded. *)
val incr : int ref -> unit

(** Same as [incr], but decrements the [int]. *)
val decr : int ref -> unit

(** Apply the given function to the given argument while taking care
    of rolling back possible changes to the state of references in
    case of exception. *)
val apply : ('a -> 'b) -> 'a -> 'b

(** Apply the given function to the given argument while taking care
    of rolling back possible changes to the state of references. *)
val pure_apply : ('a -> 'b) -> 'a -> 'b

(** Apply the given test function to the given argument and rollback
    possible changes ONLY if the value [false] is returned. *)
val pure_test : ('a -> bool) -> 'a -> bool

(** A timed ref, this ref needs a time to be accessed. *)
type 'a tref = 'a ref

(** creation of a tref *)
val tref : 'a -> 'a tref

(** A access a 'a tref with rollback before *)
val get : Time.t -> 'a tref -> 'a

(** Update a 'a tref and return the current time *)
val set : 'a tref -> 'a -> Time.t
