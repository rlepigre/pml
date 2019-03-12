(** Standard eq-type based on a GADT. *)

(** Equality type. *)
type ('a, 'b) t =
  | Eq  : ('a, 'a) t (** The types ['a] and ['b] are equal.        *)
  | NEq : ('a, 'b) t (** The types ['a] and ['b] may not be equal. *)

(** Synonym of [('a,'b) t]. *)
type ('a, 'b) eq = ('a, 'b) t

(** [x &&& y] builds a cunjunction of equalities in the form of an arrow. *)
val ( &&& ) : ('a, 'b) eq -> ('c, 'd) eq -> ('a -> 'c, 'b -> 'd) eq
