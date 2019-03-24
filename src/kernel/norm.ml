(** Higher order normalisation functions. This modules defines several
    normalisation functions for PML's abstract syntax tree. Such functions
    can be used to reduce higher-order types and to unfold unifications
    variables. *)

open Pos
open Ast

(** [repr e] unfolds surface unification variables. *)
let rec repr : type a. a ex loc -> a ex loc = fun exp ->
  match exp.elt with
  | UVar(_, {uvar_val = {contents = Set exp}})  -> repr exp
  | _                                           -> exp

(** [whnf e] normalises the expression [e] until it does not contain any
    surface redex of the form [HApp(HFun _, _)]. This function also unfolds
    surface unification variables. *)
let rec whnf : type a. a ex loc -> a ex loc = fun exp ->
  match exp.elt with
  (* Reduction of a redex. *)
  | HApp(s,e,f)                       ->
      begin
        let ne = whnf e and nf = whnf f in
        match (ne.elt, nf.elt) with
        | (HFun(_,_,b), f) -> whnf (bndr_subst b f)
        | (HDef(_,d)  , _) ->
           let de = {exp with elt = HApp(s, d.expr_def, nf)} in
           let nde = whnf de in (* preserves physical eq if possible *)
           if nde == de && ne == e && nf == f then exp else nde
        | (FixM(s,o,b,l), _) -> Pos.make exp.pos (FixM(s,o,b,Cns(nf,l)))
        | (FixN(s,o,b,l), _) -> Pos.make exp.pos (FixN(s,o,b,Cns(nf,l)))
        | (_          , _) -> (* preserves physical eq if possible *)
           if ne == e && nf == f then exp
           else {exp with elt = HApp(s, e, f)}
      end
  (* Unfolding of a unification variable. *)
  | UVar(_, {uvar_val = {contents = Set exp}})  -> whnf exp
  (* No possible surface reduction. *)
  | _                                           -> exp
