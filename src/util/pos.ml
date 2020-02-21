(** Source code position management. This module can be used to map the
    elements of an abstract syntax tree to sequences of characters in a
    source file. *)

open Pacomb

include Pos

type user = ..
type user += Nothing : user

(** Type constructor extending a type (e.g. an element of an abstract syntax
    tree) with a source code position. *)
type 'a loc =
  { elt : 'a   (** The element that is being localised.        *)
  ; pos : pos (** Position of the element in the source code. *)
  ; usr : user Timed.tref }

(** Localised string type (widely used). *)
type strloc = string loc

(** [in_pos pos elt] associates the position [pos] to [elt]. *)
let in_pos : pos -> 'a -> 'a loc =
  fun p elt -> { elt ; pos = p; usr = Timed.tref Nothing }

let make : pos option -> 'a -> 'a loc =
  fun pos elt ->
  let pos = match pos with
    | None   -> Pos.phantom_pos
    | Some p -> p
  in
  { elt ; pos; usr = Timed.tref Nothing }

(** [none elt] wraps [elt] in a localisation structure with no specified
    source position. *)
let none : 'a -> 'a loc =
  fun elt -> { elt ; pos = Pos.phantom_pos; usr = Timed.tref Nothing }

(** [print_pos oc pos] prints the position [pos] to the channel [oc]. *)
let print_pos : string ->  out_channel -> pos -> unit = fun prefix ch p ->
  if has_pos p then
    begin
      Printf.fprintf ch "%a"
        (Pos.print_pos ~style:Short ~quote:{default_quote with prefix} ()) p
    end
open Output

let print_wrn_pos     = print_pos ("[" ^ yel "WRN" ^ "] ")
let print_err_pos     = print_pos ("[" ^ red "ERR" ^ "] ")
let print_bug_pos     = print_pos ("[" ^ mag "BUG" ^ "] ")
let print_tag_pos tag = print_pos ("[" ^ cya "TAG" ^ "] ")
