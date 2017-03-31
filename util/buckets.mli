(** Simple buckets in which a key is associated to multiple values. The keys
    are compared with the equality function specified upon the creation of a
    new structure. *)

(** Type of a bucket. *)
type ('a, 'b) t

(** Synonym of [('a, 'b) t]. *)
type ('a, 'b) buckets = ('a, 'b) t

(** [empty eq] creates an empty bucket using the given equality function for
    comparing keys. *)
val empty : ('a -> 'a -> bool) -> ('a, 'b) t

(** [add key v bcks] maps the value [v] to the [key] in [bcks]. *)
val add : 'a -> 'b -> ('a, 'b) t -> ('a, 'b) t

(** [find key bcks] obtains the list of all the values associated to  [key].
    Note that this operation cannot fails and returns [[]] in the case where
    no value is assocaited to [key] in [bcks]. *)
val find : 'a -> ('a, 'b) t -> 'b list
