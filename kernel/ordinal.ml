open Extra
open Ast
open Pos
open Compare
open Sorts

type positives = (ordi * ordi option) list

let is_pos : positives -> ordi -> bool =
  fun pos o ->
    let o = Norm.whnf o in
    match o.elt with
    | Vari(_) -> assert false (* Should not happen. *)
    | Zero    -> false
    | Conv    -> true
    | Succ(_) -> true
    | _       -> List.exists (fun (c,_) -> eq_expr ~strict:true o c) pos

let candidate_pred : positives -> ordi -> ordi list = fun pos o ->
  Output.bug_msg "Looking for candidate predecessor of %a." Print.ex o;
  let rec pred acc pos =
    match pos with
    | []               -> acc
    | (k, Some p)::pos -> let acc =
                            if eq_expr ~strict:true o k then p::acc
                            else acc
                          in pred acc pos
    | _          ::pos -> pred acc pos
  in pred [] pos

let rec oadd : ordi -> int -> ordi =
  fun o n -> if n <= 0 then o else oadd (Pos.none (Succ(o))) (n-1)

let rec leq_i_ordi : positives -> ordi -> int -> ordi -> bool =
  fun pos o1 i o2 ->
    let o1 = Norm.whnf o1 in
    let o2 = Norm.whnf o2 in
    match (o1.elt, o2.elt) with
    | (Vari(_) , _       ) -> assert false (* Should not happen. *)
    | (_       , Vari(_) ) -> assert false (* Should not happen. *)
    (* TODO #54 use oracle for eq_expr *)
    | (_       , _       ) when eq_expr ~strict:true (oadd o1 i) o2 -> true
    | (_       , Succ(o2)) -> leq_i_ordi pos o1 (i-1) o2
    | (Succ(o1), _       ) -> leq_i_ordi pos o1 (i+1) o2
    | (OWMu(o1,_,_),_    )
    | (OWNu(o1,_,_),_    )
    | (OSch(Some o1,_,_), _   ) ->
        let i = if is_pos pos o1 then i-1 else i in
        leq_i_ordi pos o1 i o2
    | (Zero    , _       ) -> i <= 0 || (i = 1 && is_pos pos o2)
    | (UVar(_,v), _      ) ->
        begin
          let l = candidate_pred pos o2 in
          Output.bug_msg "There are %i candidates." (List.length l);
          match l with
          | []   when i <= 0 || (i = 1 && is_pos pos o2)
                 -> uvar_set v (Pos.none Zero); true
          | []   -> false
          | o::_ -> uvar_set v o; true
        end
    | (_       , _       ) -> false

let leq_ordi : positives -> ordi -> ordi -> bool =
  fun pos o1 o2 -> leq_i_ordi pos o1 0 o2

let less_ordi : positives -> ordi -> ordi -> bool =
  fun pos o1 o2 -> leq_i_ordi pos o1 1 o2
