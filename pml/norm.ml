(** Higher order normalisation functions. This modules defines several
    normalisation functions for PML's abstract syntax tree. Such functions
    can be used to reduce higher-order types and to unfold unifications
    variables. *)

open Bindlib
open Pos
open Ast

(** [repr e] unfolds surface unification variables. *)
let rec repr : type a. a ex loc -> a ex loc = fun exp ->
  match exp.elt with
  | UVar(_, _, {contents = Some exp}) -> repr exp
  | _                                 -> exp

(** [whnf e] normalises the expression [e] until it does not contain any
    surface redex of the form [HApp(HFun _, _)]. This function also unfolds
    surface unification variables. *)
let rec whnf : type a. a ex loc -> a ex loc = fun exp ->
  match exp.elt with
  (* Reduction of a redex. *)
  | HApp(s,e,f)                       ->
      begin
        let e = whnf e and f = whnf f in
        match (e.elt, f.elt) with
        | (HFun(b), f) -> whnf (lsubst b f)
        | (_      , _) -> {exp with elt = HApp(s, e, f)}
      end
  (* Unfolding of a unification variable. *)
  | UVar(_, _, {contents = Some exp}) -> whnf exp
  (* No possible surface reduction. *)
  | _                                 -> exp
