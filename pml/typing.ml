open Bindlib
open Sorts
open Pos
open Ast
open Equiv

exception Type_error of string
let type_error : string -> 'a =
  fun msg -> raise (Type_error(msg))

exception Subtype_error of string
let subtype_error : string -> 'a =
  fun msg -> raise (Subtype_error msg)

exception Unexpected_error of string
let unexpected : string -> 'a =
  fun msg -> raise (Unexpected_error msg)

type ctxt  = unit

type typ_rule =
  | Typ_VTyp of sub_proof * typ_proof
  | Typ_TTyp of sub_proof * typ_proof
  | Typ_VLam of typ_proof
  | Typ_TLam of typ_proof

and  sub_rule = unit

and typ_proof = term * prop * typ_rule
and sub_proof = term * prop * prop * sub_rule

let get_typ_rule : typ_proof -> typ_rule = fun (_,_,r) -> r



let rec get_lam : type a. string -> a sort -> term -> prop -> a ex =
  fun x s t c ->
    match (Norm.repr c).elt with
    | Univ(k,f) when lbinder_name f = x ->
        get_lam x s t (lsubst f (UWit(k,t,f)))
    | Univ(k,f) ->
        begin
          match eq_sort s k with
          | Eq  -> UWit(k,t,f)
          | NEq -> assert false
        end
    | _         -> assert false



let rec subtype : ctxt -> term -> prop -> prop -> sub_proof = fun ctx t a b ->
  let a = Norm.repr a in
  let b = Norm.repr b in
  let r =
    match (a,b) with
    | _ -> assert false
  in
  (t, a, b, r)

and type_valu : ctxt -> valu -> prop -> typ_proof = fun ctx v c ->
  let r =
    match (Norm.repr v).elt with
    (* λ-abstraction. *)
    | LAbs(ao,b)  ->
        assert false (* TODO *)
    (* Constructor. *)
    | Cons(c,v)   ->
        assert false (* TODO *)
    (* Record. *)
    | Reco(m)     ->
        assert false (* TODO *)
    (* Scissors. *)
    | Scis        ->
        assert false (* TODO *)
    (* Coercion. *)
    | VTyp(v,a)   ->
        let p1 = subtype ctx (build_pos v.pos (Valu(v))) a c in
        let p2 = type_valu ctx v a in
        Typ_VTyp(p1,p2)
    (* Type abstraction. *)
    | VLam(s,b)   ->
        let t = build_pos v.pos (Valu(v)) in
        let a = get_lam (lbinder_name b) s t c in
        let p = type_valu ctx (lsubst b a) c in
        Typ_VLam(p)
    (* Witness. *)
    | VWit(t,a,b) ->
        assert false (* TODO *)
    (* Constructors that cannot appear in user-defined terms. *)
    | UWit(_,_,_) -> unexpected "∀-witness during typing..."
    | EWit(_,_,_) -> unexpected "∃-witness during typing..."
    | UVar(_)     -> unexpected "unification variable during typing..."
    | Vari(_)     -> unexpected "Free variable during typing..."
    | HApp(_,_)   -> unexpected "Higher-order application during typing..."
    | Dumm        -> unexpected "Dummy value during typing..."
    | ITag(_)     -> unexpected "Tag during typing..."
  in
  (build_pos v.pos (Valu(v)), c, r)

and type_term : ctxt -> term -> prop -> typ_proof = fun ctx t c ->
  let r =
    match (Norm.repr t).elt with
    (* Value. *)
    | Valu(v)     ->
        get_typ_rule (type_valu ctx v c)
    (* Application. *)
    | Appl(t,u)   ->
        assert false (* TODO *)
    (* μ-abstraction. *)
    | MAbs(ao,b)  ->
        assert false (* TODO *)
    (* Named term. *)
    | Name(pi,t)  ->
        assert false (* TODO *)
    (* Projection. *)
    | Proj(v,l)   ->
        assert false (* TODO *)
    (* Case analysis. *)
    | Case(v,m)   ->
        assert false (* TODO *)
    (* Fixpoint. *)
    | FixY(t,v)   ->
        assert false (* TODO *)
    (* Coercion. *)
    | TTyp(t,a)   ->
        let p1 = subtype ctx t a c in
        let p2 = type_term ctx t a in
        Typ_TTyp(p1,p2)
    (* Type abstraction. *)
    | TLam(s,b)   ->
        let a = get_lam (lbinder_name b) s t c in
        let p = type_term ctx (lsubst b a) c in
        Typ_TLam(p)
    (* Constructors that cannot appear in user-defined terms. *)
    | UWit(_,_,_) -> unexpected "∀-witness during typing..."
    | EWit(_,_,_) -> unexpected "∃-witness during typing..."
    | UVar(_)     -> unexpected "unification variable during typing..."
    | Vari(_)     -> unexpected "Free variable during typing..."
    | HApp(_,_)   -> unexpected "Higher-order application during typing..."
    | Dumm        -> unexpected "Dummy value during typing..."
    | ITag(_)     -> unexpected "Tag during typing..."
  in
  (t, c, r)

