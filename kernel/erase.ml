(** Evaluation in an abstract machine. *)

open Bindlib
open Pos
open Output
open Sorts
open Ast
open Eval

exception Erasure_error of string
let erasure_error : type a. string -> a =
  fun msg -> raise (Erasure_error msg)

let rec valu_erasure : valu -> e_vbox = fun v ->
  let v = Norm.whnf v in
  match v.elt with
  | Vari(_,x) -> box_of_var (copy_var x (name_of x) mk_vvari)
  | HApp(_)   -> erasure_error "not a normalisation value (value)"
  | HDef(_,d) -> valu_erasure d.expr_def
  | LAbs(_,b) -> let f x =
                   let x = copy_var x (name_of x) (mk_free V) in
                   term_erasure (bndr_subst b (free_of x))
                 in vlabs (binder_name (snd b)) f
  | Cons(c,v) -> vcons c.elt (valu_erasure v)
  | Reco(m)   -> vreco (A.map (fun (_,v) -> valu_erasure v) m)
  | Scis      -> vscis
  | Goal(_,s) -> vscis
  | VDef(d)   -> box d.value_eval
  | VTyp(v,_) -> valu_erasure v
  | VLam(_,f) -> valu_erasure (bndr_subst f Dumm)
  | ITag(_)   -> erasure_error "a tag cannot be erased (value)"
  | Dumm      -> erasure_error "a dummy value cannot be erased (value)"
  | VWit(_)   -> erasure_error "a witness cannot be erased (value)"
  | UWit(_)   -> erasure_error "a witness cannot be erased (value)"
  | EWit(_)   -> erasure_error "a witness cannot be erased (value)"
  | UVar(_)   -> erasure_error "unif. variables cannot be erased (value)"

and     term_erasure : term -> e_tbox = fun t ->
  let t = Norm.whnf t in
  match t.elt with
  | Vari(_,x) -> box_of_var (copy_var x (name_of x) mk_tvari)
  | HApp(_)   -> erasure_error "not a normalisation value (term)"
  | HDef(_,d) -> term_erasure d.expr_def
  | Valu(v)   -> tvalu (valu_erasure v)
  | Appl(t,u) -> tappl (term_erasure t) (term_erasure u)
  | MAbs(b)   -> let f x =
                   let x = copy_var x (name_of x) (mk_free S) in
                   term_erasure (bndr_subst b (free_of x))
                 in tmabs (binder_name (snd b)) f
  | Name(s,t) -> tname (stac_erasure s) (term_erasure t)
  | Proj(v,l) -> tproj (valu_erasure v) l.elt
  | Case(v,m) -> let f (_,b) =
                   let f x =
                     let x = copy_var x (name_of x) (mk_free V) in
                     term_erasure (bndr_subst b (free_of x))
                   in (binder_name (snd b), f)
                 in tcase (valu_erasure v) (A.map f m)
  | FixY(b,v) -> let f x =
                   let x = copy_var x (name_of x) (mk_free V) in
                   term_erasure (bndr_subst b (free_of x))
                 in tfixy (binder_name (snd b)) f (valu_erasure v)
  | Prnt(s)   -> tprnt s
  | TTyp(t,_) -> term_erasure t
  | TLam(_,f) -> term_erasure (bndr_subst f Dumm)
  | ITag(_)   -> erasure_error "a tag cannot be erased (term)"
  | Dumm      -> erasure_error "a dummy value cannot be erased (term)"
  | UWit(_)   -> erasure_error "a witness cannot be erased (term)"
  | EWit(_)   -> erasure_error "a witness cannot be erased (term)"
  | UVar(_)   -> erasure_error "unif. variables cannot be erased (term)"
  | Goal(_)   -> erasure_error "a goal cannot be erased (term)"

and     stac_erasure : stac -> e_sbox = fun s ->
  let s = Norm.whnf s in
  match s.elt with
  | Vari(_,x) -> box_of_var (copy_var x (name_of x) mk_svari)
  | HApp(_)   -> erasure_error "not a normalisation value (stack)"
  | HDef(_,d) -> stac_erasure d.expr_def
  | Epsi      -> sepsi
  | Goal(_)   -> sepsi
  | Push(v,s) -> spush (valu_erasure v) (stac_erasure s)
  | Fram(t,s) -> sfram (term_erasure t) (stac_erasure s)
  | ITag(_)   -> erasure_error "a tag cannot be erased (stack)"
  | Dumm      -> erasure_error "a dummy value cannot be erased (stack)"
  | SWit(_,_) -> erasure_error "a witness cannot be erased (stack)"
  | UWit(_)   -> erasure_error "a witness cannot be erased (stack)"
  | EWit(_)   -> erasure_error "a witness cannot be erased (stack)"
  | UVar(_)   -> erasure_error "unif. variables cannot be erased (stack)"


let valu_erasure : valu -> e_valu =
  fun v -> unbox (valu_erasure v)

let term_erasure : term -> e_term =
  fun t -> unbox (term_erasure t)

let stac_erasure : stac -> e_stac =
  fun s -> unbox (stac_erasure s)

(* Conversion of erased expression to expression. *)

(** Evaluation in an abstract machine. *)
let rec to_valu : e_valu -> vbox = fun v ->
  match v with
  | VVari(x)   -> vari None (copy_var x (name_of x) (mk_free V))
  | VLAbs(b)   -> let f x =
                    let x = copy_var x (name_of x) mk_vvari in
                    to_term (subst b (free_of x))
                  in labs None None (Pos.none (binder_name b)) f
  | VCons(c,v) -> cons None (Pos.none c) (to_valu v)
  | VReco(m)   -> reco None (A.map (fun v -> (None, to_valu v)) m)
  | VScis      -> scis None

and to_term : e_term -> tbox = fun t ->
  match t with
  | TVari(a)   -> vari None (copy_var a (name_of a) (mk_free T))
  | TValu(v)   -> valu None (to_valu v)
  | TAppl(t,u) -> appl None (to_term t) (to_term u)
  | TMAbs(b)   -> let f x =
                    let x = copy_var x (name_of x) mk_svari in
                    to_term (subst b (free_of x))
                  in mabs None (Pos.none (binder_name b)) f
  | TName(s,t) -> name None (to_stac s) (to_term t)
  | TProj(v,l) -> proj None (to_valu v) (Pos.none l)
  | TCase(v,m) -> let f b =
                    let f x =
                      let x = copy_var x (name_of x) mk_vvari in
                      to_term (subst b (free_of x))
                    in (None, Pos.none (binder_name b), f)
                  in case None (to_valu v) (A.map f m)
  | TFixY(b,v) -> let f x =
                    let x = copy_var x (name_of x) mk_vvari in
                    to_term (subst b (free_of x))
                  in
                  fixy None (Pos.none (binder_name b)) f (to_valu v)
  | TPrnt(s)   -> prnt None s

and to_stac : e_stac -> sbox = fun s ->
  match s with
  | SVari(a)   -> vari None (copy_var a (name_of a) (mk_free S))
  | SEpsi      -> epsi None
  | SPush(v,s) -> push None (to_valu v) (to_stac s)
  | SFram(t,s) -> fram None (to_term t) (to_stac s)

let to_valu : e_valu -> valu =
  fun v -> unbox (to_valu v)

let to_term : e_term -> term =
  fun t -> unbox (to_term t)

let to_stac : e_stac -> stac =
  fun s -> unbox (to_stac s)
