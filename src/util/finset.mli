(** This module implements a constraint solver for finite sets *)

open Timed

module type Elt = sig
  type t

  val all : t list
  val print : out_channel -> t -> unit
end

module type FinSet = sig
  type elt
  type set = elt list
  (** type of a set of elt or a variable representing such a set *)
  type t

  (** construct a fixed set *)
  val known : elt list -> t
  (** full and empty set *)
  val bot   : t
  val top   : t

  (** creates a new variable representing a set. Optional parameters allows for
  initial constraints *)
  val create : ?absent:set -> ?present:set -> unit -> t

  (** returns Some l is the set is fully known *)
  val complete : t -> elt list option

  (** returns true is the elt is in the set of the constraint to add it if
  consistent with the current constraints. No constraints are added if the
  function returns false *)
  val present : elt -> t -> bool

  (** returns true is the elt is not in the set of the constraint to remove
  it if consistent with the current constraints. No constraints are added if
  the function returns false *)
  val absent : elt -> t -> bool

  (** [sub s1 s2] test or force the constraints s1 subset of s2.
      [sub ~except:s0 s1 s2] test for s1 < (s2 union s0) which is
      the same as (s1 inter s0) < s2 *)
  val sub : ?except:set -> t -> t -> bool

  (** test for equality of add the constraint *)
  val eq : t -> t -> bool

  (** test subset in the current knowledge, but do not add any constraint *)
  val know_sub : t -> set -> bool

  (** test equality in the current knowledge.
      TODO: incomplete in the current version, may return false while the equality
      is known *)
  val know_eq : t -> t -> bool

  val know_absent : elt -> t -> bool
  val know_present : elt -> t -> bool

  val hash : t -> int
end

module Make(T:Timed)(E:Elt) : FinSet with type elt = E.t
