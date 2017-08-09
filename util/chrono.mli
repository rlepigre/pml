(** Small timer library for timing the application of functions. *)

(** [time rt fn x] times the computation of [fn x]. Its computation time (in
    seconds) is then fed to the function [rt]. *)
val time : (float -> unit) -> ('a -> 'b) -> 'a -> 'b

(** Type of a timer. *)
type chrono

(** Synonym of [chrono]. *)
type t = chrono

(** [create name] create a new timer with the name [name]. *)
val create : string -> t

(** [add_time chr fn x] times the computation of [fn x] with [chr]. Note the
    computation time is accumulated with all the computations times with the
    timer [chr]. *)
val add_time : t -> ('a -> 'b) -> 'a -> 'b

(** [get_name chr] gets the name of the timer [chr]. *)
val get_name  : t -> string

(** [get_time chr] gets the current time (in seconds) stored in [chr]. *)
val get_time  : t -> float

(** [get_count chr] gets the number of function calls timed using [chr]. *)
val get_count : t -> int

(** [iter fn] calls [fn name time count] with the [name], [time] and [count]
    of all the timers on the system. *)
val iter : (string -> float -> int -> unit) -> unit
