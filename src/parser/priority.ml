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

(* Comparison of mode for priorities *)
let (<<=) = fun p1 p2 ->
  match p1, p2 with
  | _     , HO     -> true
  | Any   ,_       -> true
  | Prp p1, Prp p2 -> p1 <= p2
  | Trm p1, Trm p2 -> p1 <= p2
  | Stk   , Stk    -> true
  | Ord p1, Ord p2 -> p1 <= p2
  | _     , _      -> false

let reset = function
  | Any   -> Any
  | HO    -> Any
  | Prp _ -> Prp F
  | Trm _ -> Trm F
  | Ord _ -> Ord F
  | Stk   -> Stk
