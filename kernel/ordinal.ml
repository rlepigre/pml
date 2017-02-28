open Ast
open Pos
open Compare

type positives = ordi list

let is_pos : positives -> ordi -> bool =
  fun pos o ->
    let o = Norm.whnf o in
    match o.elt with
    | Vari(_) -> assert false (* Should not happen. *)
    | Conv    -> true
    | Succ(_) -> true
    | _       -> List.exists (eq_expr ~strict:true o) pos

let rec oadd : ordi -> int -> ordi =
  fun o n -> if n <= 0 then o else oadd (Pos.none (Succ(o))) (n-1)

let rec leq_i_ordi : positives -> ordi -> int -> ordi -> bool =
  fun pos o1 i o2 ->
    let o1 = Norm.whnf o1 in
    let o2 = Norm.whnf o2 in
    match (o1.elt, o2.elt) with
    | (Vari(_) , _       ) -> assert false (* Should not happen. *)
    | (_       , Vari(_) ) -> assert false (* Should not happen. *)
    | (_       , _       ) when eq_expr ~strict:true (oadd o1 i) o2 -> true
    | (_       , Succ(o2)) -> leq_i_ordi pos o1 (i-1) o2
    | (Succ(o1), _       ) -> leq_i_ordi pos o1 (i+1) o2
    (*
    (* the existing constraint is enough *)
    | (OUVar({uvar_state = {contents = Unset (_, Some o')}},os), o2)
         when strict (leqi_ordi pos (msubst o' os) (i-1)) o2 -> true
    | (o1         , OUVar({uvar_state = {contents = Unset (Some o',_)}},os))
         when strict (leqi_ordi pos o1 i) (msubst o' os) -> true
    (* variable on the right, we improve the lower bound *)
    | (o1         , OUVar(p,os)) when not !eq_strict &&
        Timed.pure_test (fun () ->
          let o1 = oadd o1 i in
          less_opt_ordi pos o1 (uvar_state p) os) () ->
       p.uvar_state := Unset(Some (!fobind_ordis os (oadd o1 i)), snd (uvar_state p));
       leqi_ordi pos o1 i o2
    | (OUVar(p,os)   , o2      ) when i<=0 && safe_set_ouvar pos p os o2 ->
       leqi_ordi pos o1 i o2
    | (OLess(o1,_),       o2  ) when o1 <> OMaxi ->
       let i = if is_positive pos o1 then i-1 else i in
       leqi_ordi pos o1 i o2
    *)
    | (_       , _       ) -> false

let leq_ordi : positives -> ordi -> ordi -> bool =
  fun pos o1 o2 -> leq_i_ordi pos o1 0 o2

let less_ordi : positives -> ordi -> ordi -> bool =
  fun pos o1 o2 -> leq_i_ordi pos o1 1 o2
