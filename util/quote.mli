(** A module for quoting extracts of a text file. *)

(** [get_from_to fname off1 off2] returns the list of the lines of the file
    [fname] starting at the [off1]-th line to the [off2]-th line. Lines not
    in range are ignored. *)
val get_lines : string -> int -> int -> string list

(** Type for the configuration of the quoting function. *)
type config =
  { leading  : int    (** Number of lines before the quoted section. *)
  ; trailing : int    (** Numbef of lines after the quoted section.  *)
  ; numbers  : bool   (** Print line numbers if [true].              *)
  ; prefix   : string (** Prefix added to all the lines produced.    *) }

(** Default configuration (two leading and trailing lines, numbering of the
    lines, no prefix). *)
val default_config : config

(** Exception raised in cas of an error (e.g., invalid position). *)
exception Quote_error of Pos.pos * string

(** [quote_file ~config och pos] prints on [och] the extract of code at the
    position [pos] according the the [config]. In case of a problem (e.g. a
    non-existant file) the exception [Quote_error(pos,msg)] is raised. *)
val quote_file : ?config:config -> out_channel -> Pos.pos -> unit
