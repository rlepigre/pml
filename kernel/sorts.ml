(** Abstract representation of sorts. This module defines the representation
    of PML's sorts using a GADT. *)

type o = O_ (** "Phantom" type for the sort of ordinals. *)
type p = P_ (** "Phantom" type for the sort of types.    *)
type v = V_ (** "Phantom" type for the sort of values.   *)
type t = T_ (** "Phantom" type for the sort of terms.    *)
type s = S_ (** "Phantom" type for the sort of stacks.   *)

(** Representation of our sorts. *)
type _ sort =
  (** The sort of ordinals.     *)
  | O : o sort
  (** The sort of propositions. *)
  | P : p sort
  (** The sort of values.       *)
  | V : v sort
  (** The sort of terms.        *)
  | T : t sort
  (** The sort of stacks.       *)
  | S : s sort
  (** The arrow sort.           *)
  | F : 'a sort * 'b sort -> ('a -> 'b) sort

(** Equality function over sorts. *)
let rec eq_sort : type a b. a sort -> b sort -> (a,b) Eq.t = fun s1 s2 ->
  let open Eq in
  match (s1, s2) with
  | (V       , V       ) -> Eq
  | (T       , T       ) -> Eq
  | (S       , S       ) -> Eq
  | (P       , P       ) -> Eq
  | (O       , O       ) -> Eq
  | (F(a1,b1), F(a2,b2)) -> eq_sort a1 a2 &&& eq_sort b1 b2
  | (_       , _       ) -> NEq

(** Filter type for the sorts of terms and values. *)
type _ v_or_t =
  | VoT_V : v v_or_t
  | VoT_T : t v_or_t

(** Filter type for the sorts of terms and values. *)
type _ v_or_s =
  | VoS_V : v v_or_s
  | VoS_S : s v_or_s

(** Description type for a vector of sort-indexed objects. *)
type _ desc =
  | LastS : 'a sort           -> 'a        desc
  | MoreS : 'a sort * 'b desc -> ('a * 'b) desc
