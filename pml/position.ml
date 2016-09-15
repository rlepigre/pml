(** Source code position management. This module can be used to map the
    elements of an abstract syntax tree to sequences of characters in a
    source file. *)


(** Type of a position corresponding to a continuous range of characters in
    a (utf8 encoded) source file. *)
type pos =
  { fname      : string (** File name associated to the position.       *)
  ; start_line : int    (** Line number of the starting point.          *)
  ; start_col  : int    (** Column number (utf8) of the starting point. *)
  ; end_line   : int    (** Line number of the ending point.            *)
  ; end_col    : int    (** Column number (utf8) of the ending point.   *)
  }

(** Type constructor extending a type (e.g. an element of an abstract syntax
    tree) with a source code position. *)
type 'a loc =
  { elt : 'a            (** The element that is being localised.        *)
  ; pos : pos option    (** Position of the element in the source code. *)
  }

(** Localised string type (widely used). *)
type strloc = string loc


(** [in_pos pos elt] associates the position [pos] to [elt]. *)
let in_pos : pos -> 'a -> 'a loc =
  fun p elt -> { elt ; pos = Some p }

(** [none elt] wraps [elt] in a localisation structure with no specified
    source position. *)
let none : 'a -> 'a loc =
  fun elt -> { elt ; pos = None }

(** [locate buf1 pos1 buf2 pos2] builds a position structure given two
    DeCaP input buffers. This function can be used by DeCaP to generate
    the position of elements during parsing.
    @see <http://lama.univ-savoie.fr/decap/> DeCap *)
let locate buf1 pos1 buf2 pos2 =
  { fname      = Input.fname buf1
  ; start_line = Input.line_num buf1
  ; start_col  = Input.utf8_col_num buf1 pos1
  ; end_line   = Input.line_num buf2
  ; end_col    = Input.utf8_col_num buf2 pos2
  }
