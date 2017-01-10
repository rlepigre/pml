(** Evaluation in an abstract machine. *)

open Bindlib
open Pos
open Ast
open Eval

exception Erasure_error of string
let erasure_error : type a. string -> a =
  fun msg -> raise (Erasure_error msg)

let rec valu_erasure : valu -> e_vbox = fun v ->
  let v = Norm.whnf v in
  match v.elt with
  | Vari(x)   -> box_of_var (copy_var x (name_of x) mk_vvari)
  | HApp(_)   -> erasure_error "not a normalisation value (value)"
  | HDef(_,d) -> valu_erasure d.expr_def
  | LAbs(_,b) -> let f x =
                   let x = copy_var x (name_of x) mk_free in
                   term_erasure (bndr_subst b (free_of x))
                 in vlabs (binder_name (snd b)) f
  | Cons(c,v) -> vcons c.elt (valu_erasure v)
  | Reco(m)   -> vreco (M.map (fun (_,v) -> valu_erasure v) m)
  | Scis      -> vscis
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
  | Vari(x)   -> box_of_var (copy_var x (name_of x) mk_tvari)
  | HApp(_)   -> erasure_error "not a normalisation value (term)"
  | HDef(_,d) -> term_erasure d.expr_def
  | Valu(v)   -> tvalu (valu_erasure v)
  | Appl(t,u) -> tappl (term_erasure t) (term_erasure u)
  | MAbs(_,b) -> let f x =
                   let x = copy_var x (name_of x) mk_free in
                   term_erasure (bndr_subst b (free_of x))
                 in tmabs (binder_name (snd b)) f
  | Name(s,t) -> tname (stac_erasure s) (term_erasure t)
  | Proj(v,l) -> tproj (valu_erasure v) l.elt
  | Case(v,m) -> let f (_,b) =
                   let f x =
                     let x = copy_var x (name_of x) mk_free in
                     term_erasure (bndr_subst b (free_of x))
                   in (binder_name (snd b), f)
                 in tcase (valu_erasure v) (M.map f m)
  | FixY(t,v) -> tfixy (term_erasure t) (valu_erasure v)
  | TTyp(t,_) -> term_erasure t
  | TLam(_,f) -> term_erasure (bndr_subst f Dumm)
  | ITag(_)   -> erasure_error "a tag cannot be erased (term)"
  | Dumm      -> erasure_error "a dummy value cannot be erased (term)"
  | UWit(_)   -> erasure_error "a witness cannot be erased (term)"
  | EWit(_)   -> erasure_error "a witness cannot be erased (term)"
  | UVar(_)   -> erasure_error "unif. variables cannot be erased (term)"

and     stac_erasure : stac -> e_sbox = fun s ->
  let s = Norm.whnf s in
  match s.elt with
  | Vari(x)   -> box_of_var (copy_var x (name_of x) mk_svari)
  | HApp(_)   -> erasure_error "not a normalisation value (stack)"
  | HDef(_,d) -> stac_erasure d.expr_def
  | Epsi      -> sepsi
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
