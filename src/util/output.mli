(** Colorful outputs / logs. A very simple module providing colorfull output
    utilities for logs (or log file), warnings and errors. Integration  with
    command line arguments parsing is made easy. *)

(** Type of printf-like functions. *)
type 'a formatter = ('a, out_channel, unit) format -> 'a

(** Always use escape sequences for colors (even in a pipe). *)
val always_colors : bool ref

(** Main printing function (to standard output). It is actually the same  as
    [Printf.printf]. *)
val out     : 'a formatter

(** Printing function for a warning message, printed in yellow and preceeded
    by the ["[WRN]"] tag. Note that a newline symbol is append to the format
    and that the channel is flushed. *)
val wrn_msg : 'a formatter

(** Printing function for an error message, printed in red and preceeded  by
    the ["[ERR]"] tag. Note that a newline symbol is append  to  the  format
    and that the channel is flushed. *)
val err_msg : 'a formatter

(** Printing function for a bug signaling message, printed  in  magenta  and
    preceeded by the ["[BUG]"] tag. Note that a newline symbol is append  to
    the format and that the channel is flushed. *)
val bug_msg : 'a formatter

module Log :
  sig
    (** Log management module. Note that by default, logs are printed on the
        standard [stderr] channel. Note that each log ently is preceeded  by
        a short three character description. *)

    (** After calling [with_file fname], the logs are printed to [fname]. If
        the file already exists, it is overwritten. *)
    val with_file : string -> unit

    (** After calling [with_out_channel och], the logs are  printed  to  the
        [och] output channel. Note that it is the user's  responsibility  to
        close the channel when all the log messages have been written. *)
    val with_out_channel : out_channel -> unit

    (** [log ~tag ...] append (unconditionally) a message to  the  log.  The
        optional [tag] argument can be used to set the three  characters tag
        associated to the entry. Note that a newline character is append  to
        the message automatically, and that the buffer is flushed. *)
    val log : ?tag:string -> 'a formatter

    (** Type of a formatter wrapped in a record. This type is useful  to  work
        around value restriction... *)
    type r_formatter = { p : 'a. 'a formatter }

    (** [register key tag descr] registers a new logging function associated
        to a character [key], an optional three character [tag] and a descr-
        iption message [descr]. Logs written using the returned function are
        only printed to the log if the [key] has been enabled. Note  that  a
        newline character is append to the message automatically,  and  that
        the buffer is flushed when using the produced log function. *)
    val register : char -> string option -> string -> r_formatter

    (** [enable c] enables the log function associated to the key [c]. *)
    val enable : char -> unit

    (** [disable c] disables the log function associated to the key [c]. *)
    val disable : char -> unit

    (** [set_enabled str] set the enabled log functions to be exactly  those
        which key is contained in the string [str]. *)
    val set_enabled : string -> unit

    (** [get_enabled ()] returns a string containing the representation of
        the enabled logs. *)
    val get_enabled : unit -> string

    (** [without fn e] computed [fn e] with all the logs disabled. The logs
        are restored even if an exception is raised by the computation. *)
    val without : ('a -> 'b) -> 'a -> 'b

    (** [print_opts ~prefix och] prints on the output channel [och] a  short
        summary of all the registered log functions (and their  keys).  Each
        line of this list is preceeded with an optional [prefix]. *)
    val print_opts : ?prefix:string -> out_channel -> unit

    (** [opts_to_string prefix] build a string containing a short summary of
        all the registered log functions (and their keys). Each line of this
        list is preceeded with the given [prefix]. *)
    val opts_to_string : string -> string
  end

(** Type of a printing function for elements of type ['a]. *)
type 'a printer = out_channel -> 'a -> unit

(** [print_list pelem sep l] prints the list [l] using the function  [pelem]
    ofr printing its elements, and [sep] as a separator. *)
val print_list : 'a printer -> string -> 'a list printer

(** [print_array] is the same as [print_list], but for the [array] type. *)
val print_array : 'a printer -> string -> 'a array printer

val yel : string -> string
val red : string -> string
val mag : string -> string
val cya : string -> string
