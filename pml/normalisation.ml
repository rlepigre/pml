(** Higher order normalisation functions. This modules defines several
    normalisation functions for PML's abstract syntax tree. Such functions
    can be used to reduce higher-order types and to unfold unifications
    variables. *)

open Bindlib
open Position
open Ast

(** [repr e] unfolds surface unification variables. *)
let rec repr : type a. a ex loc -> a ex loc = fun exp ->
  match exp.elt with
  | UVar({contents = Some exp}) -> repr exp
  | _                           -> exp

(** [whnf e] normalises the expression [e] until it does not contain any
    surface redex of the form [HApp(HFun _, _)]. This function also unfolds
    surface unification variables. *)
let rec whnf : type a. a ex loc -> a ex loc = fun exp ->
  match exp.elt with
  (* Reduction of a redex. *)
  | HApp(e,f)                   ->
      begin
        let e = whnf e and f = whnf f in
        match (e.elt, f.elt) with
        | (HFun(b), f) -> whnf (lsubst b f)
        | (e      , f) -> {exp with elt = HApp(Obj.magic e, Obj.magic f)}
      end
  (* Unfolding of a unification variable. *)
  | UVar({contents = Some exp}) -> whnf exp
  (* No possible surface reduction. *)
  | _                           -> exp

(** [full_nf e] normalises completely the expression [e]. *)
let rec full_nf : type a. a ex loc -> a ex loc = fun exp ->
  match exp.elt with
  (* Reduction of a redex. *)
  | HApp(e,f)                   ->
      begin
        let e = full_nf e and f = full_nf f in
        match (e.elt, f.elt) with
        | (HFun(b), f) -> full_nf (lsubst b f)
        | (e      , f) -> {exp with elt = HApp(Obj.magic e, Obj.magic f)}
      end
  (* Unfolding of a unification variable. *)
  | UVar({contents = Some exp}) -> full_nf exp
  (* normalising under the constructors. *)
  | Func(a,b)  -> {exp with elt = Func(full_nf a, full_nf b)}
  | Prod(m)    -> let f (p, e) = (p, full_nf e) in
                  {exp with elt = Prod(M.map f m)}
  | DSum(m)    -> let f (p, e) = (p, full_nf e) in
                  {exp with elt = DSum (M.map f m)}
  | Univ(b)    -> {exp with elt = Univ(lbinder_cmp b full_nf)}
  | Exis(b)    -> {exp with elt = Exis(lbinder_cmp b full_nf)}
  | FixM(o,b)  -> {exp with elt = FixM(full_nf o, lbinder_cmp b full_nf)}
  | FixN(o,b)  -> {exp with elt = FixN(full_nf o, lbinder_cmp b full_nf)}
  | Memb(t,a)  -> {exp with elt = Memb(full_nf t, full_nf a)}
  | Rest(a,e)  -> let (t1,b,t2) = e in
                  let e = (full_nf t1, b, full_nf t2) in
                  {exp with elt = Rest(full_nf a, e)}
  | LAbs(ao,b) -> let ao = Util.map_opt full_nf ao in
                  {exp with elt = LAbs(ao, lbinder_cmp b full_nf)}
  | Cons(c,v)  -> {exp with elt = Cons(c, full_nf v)}
  | Reco(m)    -> let f (p, e) = (p, full_nf e) in
                  {exp with elt = Reco(M.map f m)}
  | Valu(v)    -> {exp with elt = Valu(full_nf v)}
  | Appl(t,u)  -> {exp with elt = Appl(full_nf t, full_nf u)}
  | MAbs(b)    -> {exp with elt = MAbs(lbinder_cmp b full_nf)}
  | Name(s,t)  -> {exp with elt = Name(full_nf s, full_nf t)}
  | Proj(v,l)  -> {exp with elt = Proj(full_nf v, l)}
  | Case(v,m)  -> let f (p, b) = (p, lbinder_cmp b full_nf) in
                  {exp with elt = Case(full_nf v, M.map f m)}
  | FixY(t,v)  -> {exp with elt = FixY(full_nf t, full_nf v)}
  | Push(v,s)  -> {exp with elt = Push(full_nf v, full_nf s)}
  | Fram(t,s)  -> {exp with elt = Fram(full_nf t, full_nf s)}
  | Succ(o)    -> {exp with elt = Succ(full_nf o)}
  | DPrj(t,x)  -> {exp with elt = DPrj(full_nf t, x)}
  | VTyp(v,a)  -> {exp with elt = VTyp(full_nf v, full_nf a)}
  | TTyp(t,a)  -> {exp with elt = TTyp(full_nf t, full_nf a)}
  | VLam(b)    -> {exp with elt = VLam(lbinder_cmp b full_nf)}
  | TLam(b)    -> {exp with elt = TLam(lbinder_cmp b full_nf)}
  (* Nothing to do. *)
  | Vari(_)   -> exp
  | HFun(_)   -> exp
  | Scis      -> exp
  | Epsi      -> exp
  | Conv      -> exp
  | ITag(_)   -> exp
  | UVar(_)   -> exp
  | VWit(_)   -> exp
  | SWit(_)   -> exp
  | UWit(_)   -> exp
  | EWit(_)   -> exp
