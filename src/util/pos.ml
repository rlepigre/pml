(** Source code position management. This module can be used to map the
    elements of an abstract syntax tree to sequences of characters in a
    source file. *)

open Pacomb

(** Convenient short name for an optional position. *)
type pos = Pos.interval
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

let merge : pos -> pos -> pos = fun ({ start = lazy s1; end_ = lazy e1 } as p1)
                                    ({ start = lazy s2; end_ = lazy e2 } as p2) ->
  match compare s1.line s2.line with
  | n when n < 0 ->
     {p1 with end_ = lazy { e1 with line = e2.line ; col = e2.col}}
  | n when n > 0 ->
     {p2 with end_ = lazy { e2 with line = e1.line ; col = e1.col}}
  | _ (* n=0 *)  -> let start_col = min s1.col s2.col in
                    let end_col   = max s1.col s2.col in
                    { start = lazy { s1 with col = start_col }
                    ; end_  = lazy { e1  with col = end_col   }}

let union : popt -> popt -> popt = fun p1 p2 ->
  match (p1, p2) with
  | (None   , None   ) -> None
  | (Some _ , None   ) -> p1
  | (None   , Some _ ) -> p2
  | (Some p1, Some p2) -> Some (merge p1 p2)

(** [print_pos oc pos] prints the position [pos] to the channel [oc]. *)
let print_pos : out_channel -> pos -> unit =
  Pos.print_interval ()

(** [print_pos oc pos] prints the position [pos] to the channel [oc]. *)
let print_pos_opt : out_channel -> popt -> unit =
  fun ch p ->
    match p with
    | None   -> output_string ch "at an unknown location"
    | Some p -> print_pos ch p

(** [print_short_pos oc pos] prints the position [pos] to the channel [oc]
    using a shorter format that [print_pos oc pos]. *)
let print_short_pos : out_channel -> pos -> unit =
  Pos.print_interval ~style:Short ()

(** [print_pos oc pos] prints the position [pos] to the channel [oc]. *)
let print_short_pos_opt : out_channel -> popt -> unit =
  fun ch p ->
    match p with
    | None   -> output_string ch "at an unknown location"
    | Some p -> print_short_pos ch p
