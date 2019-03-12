(* Priorities for parsing propositions (Atom, Memb, Rest, Prod, Full).
   F' is used to avoid the injection term -> prop inside parenthesis
   otherwise, it is ambiguous *)
type p_prio = F' | F | P | R | M | A

(* Priorities for parsing terms (Atom, aPpl, Infix, pRefix, Sequ, Full). *)
type t_prio = F | S | R | I | P | A

(* Priorities for parsing ordinals (Exponent, Full) *)
type o_prio = F | E

(* Parsing mode for expressions. *)
type mode = Any | Prp of p_prio | Trm of t_prio | Stk | Ord of o_prio | HO
