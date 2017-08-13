open Extra
open Ast
open Pos
open Compare
open Sorts
open Output

(* Log functions registration. *)
let log_ord = Log.register 'o' (Some "ord") "ordinal comparison"
let log_ord = Log.(log_ord.p)

type positives = (ordi * ordi) list

let is_pos : positives -> ordi -> bool =
  fun pos o ->
    let o = Norm.whnf o in
    match o.elt with
    | Vari(_) -> assert false (* Should not happen. *)
    | Conv    -> true
    | Succ(_) -> true
    | _       -> List.exists (fun (c,_) -> eq_expr ~strict:true o c) pos

let candidate_pred : positives -> ordi -> ordi list = fun pos o ->
  Output.bug_msg "Looking for candidate predecessor of %a." Print.ex o;
  let rec pred acc pos =
    match pos with
    | []               -> acc
    | (k, p)::pos -> let acc =
                       if eq_expr ~strict:true o k then p::acc
                       else acc
                     in pred acc pos
  in pred [] pos

let rec oadd : ordi -> int -> ordi =
  fun o n -> if n <= 0 then o else oadd (Pos.none (Succ(o))) (n-1)

(** leq_i_ordi o1 i o2 tests if
    S^i o1 <= o2 when i >= 0
    and
    o1 <= S^|i| o2 when i < 0 *)
let rec leq_i_ordi : positives -> ordi -> int -> ordi -> bool =
  fun pos o1 i o2 ->
    let o1 = Norm.whnf o1 in
    let o2 = Norm.whnf o2 in
    log_ord "%a ≤_%d %a" Print.ex o1 i Print.ex o2;
    match (o1.elt, o2.elt) with
    | _ when o1.elt == o2.elt && i <= 0 -> true
    | (Vari(_) , _       ) -> assert false (* Should not happen. *)
    | (_       , Vari(_) ) -> assert false (* Should not happen. *)
    (* TODO #54 use oracle for eq_expr *)
    | (_       , _       ) when i >= 0 && eq_expr (oadd o1 i) o2    -> true
    | (_       , _       ) when i <  0 && eq_expr o1 (oadd o2 (-i)) -> true
    | (_       , Succ(o2)) -> leq_i_ordi pos o1 (i-1) o2
    | (Succ(o1), _       ) -> leq_i_ordi pos o1 (i+1) o2
    | (OWMu(o,_,_),_     )
    | (OWNu(o,_,_),_     )
    | (OSch(Some o,_,_),_) -> let i = if is_pos pos o then i-1 else i in
                              leq_i_ordi pos o i o2
    | (_       , _       ) -> try let (_,o) = List.find (fun (o,_) -> eq_expr ~strict:true o o2) pos in
                                  leq_i_ordi pos o1 (i-1) o
                              with Not_found -> false

let ordi_chrono = Chrono.create "ordi"

let leq_ordi : positives -> ordi -> ordi -> bool =
  fun pos o1 o2 -> Chrono.add_time ordi_chrono (leq_i_ordi pos o1 0) o2

let less_ordi : positives -> ordi -> ordi -> bool =
  fun pos o1 o2 -> Chrono.add_time ordi_chrono (leq_i_ordi pos o1 1) o2
