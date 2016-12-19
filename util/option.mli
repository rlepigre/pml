(** A module for the [option] type. It should probably be  provided  by  the
    standard library. *)

(* type 'a option = None | Some of 'a *)

(** Synonym of the option type (useful for direct functor application). *)
type 'a t = 'a option

(** Synonym of the [None] constructor. *)
val none : 'a option

(** [some x] wraps [x] in the [option] type using the [Some] constructor. *)
val some : 'a -> 'a option

(** [default d xo] reads the value stored in [xo], or  returns  the  default
    value [d] if [xo] is [None]. *)
val default : 'a -> 'a option -> 'a

(** [udefault] is the same as [default] but [()] is passed  to  the  default
    value when it is used. This is useful when producing the  default  value
    requires side-effects. *)
val udefault : (unit -> 'a) -> 'a option -> 'a

(** [map f xo] applies the function [f] to the value stored in [xo]. *)
val map : ('a -> 'b) -> 'a option -> 'b option

(** [default_map] is a combination of [map] and [default]. *)
val default_map : 'b -> ('a -> 'b) -> 'a option -> 'b

(** [udefault_map] is a combination of [map] and [udefault]. *)
val udefault_map : (unit -> 'b) -> ('a -> 'b) -> 'a option -> 'b

(** [iter f xo] applies [f] to the value stored in [xo]. *)
val iter : ('a -> unit) -> 'a option -> unit

(** [equal f xo yo] compares [xo] and [yo] for equality using  the  function
    [f] in the case where both of them contain a value. *)
val equal : ('a -> 'a -> bool) -> 'a option -> 'a option -> bool

(** [compare cmp xo yo] compares [xo] and [yo] using [cmp]. Note that [None]
    is considered smaller then [Some x] whatever the value of [x]. *)
val compare : ('a -> 'a -> int) -> 'a option -> 'a option -> int
