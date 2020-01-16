(** Source code position management. This module can be used to map the
    elements of an abstract syntax tree to sequences of characters in a
    source file. *)

open Pacomb

(** Convenient short name for an optional position. *)
type pos = Pos.t * Pos.t
type popt = pos option

type user = ..
type user += Nothing : user

(** Type constructor extending a type (e.g. an element of an abstract syntax
    tree) with a source code position. *)
type 'a loc =
  { elt : 'a   (** The element that is being localised.        *)
  ; pos : popt (** Position of the element in the source code. *)
  ; usr : user Timed.tref }

(** Localised string type (widely used). *)
type strloc = string loc

(** [make pos elt] associates the position [pos] to [elt]. *)
let make : popt -> 'a -> 'a loc =
  fun pos elt -> { elt ; pos; usr = Timed.tref Nothing }

(** [in_pos pos elt] associates the position [pos] to [elt]. *)
let in_pos : pos -> 'a -> 'a loc =
  fun p elt -> { elt ; pos = Some p; usr = Timed.tref Nothing }

(** [none elt] wraps [elt] in a localisation structure with no specified
    source position. *)
let none : 'a -> 'a loc =
  fun elt -> { elt ; pos = None; usr = Timed.tref Nothing }

let merge : pos -> pos -> pos = fun ((infos,p1), (_,p2)) ((_,q1),(_,q2)) ->
  ((infos, min p1 q1), (infos, max p2 q2))


let union : popt -> popt -> popt = fun p1 p2 ->
  match (p1, p2) with
  | (None   , None   ) -> None
  | (Some _ , None   ) -> p1
  | (None   , Some _ ) -> p2
  | (Some p1, Some p2) -> Some (merge p1 p2)

(** [print_pos oc pos] prints the position [pos] to the channel [oc]. *)
let print_pos : out_channel -> pos -> unit =
  Pos.print_spos2 ()

(** [print_pos oc pos] prints the position [pos] to the channel [oc]. *)
let print_pos_opt : out_channel -> popt -> unit =
  fun ch p ->
    match p with
    | None   -> output_string ch "at an unknown location"
    | Some p -> print_pos ch p

(** [print_short_pos oc pos] prints the position [pos] to the channel [oc]
    using a shorter format that [print_pos oc pos]. *)
let print_short_pos : out_channel -> pos -> unit =
  Pos.print_spos2 ~style:Short ()

(** [print_pos oc pos] prints the position [pos] to the channel [oc]. *)
let print_short_pos_opt : out_channel -> popt -> unit =
  fun ch p ->
    match p with
    | None   -> output_string ch "at an unknown location"
    | Some p -> print_short_pos ch p
