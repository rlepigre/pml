open Bindlib
open Pos
open Ast

exception Type_error of string
let type_error : string -> 'a =
  fun msg -> raise (Type_error(msg))

exception Subtype_error of string
let subtype_error : string -> 'a =
  fun msg -> raise (Subtype_error msg)

exception Unexpected_error of string
let unexpected : string -> 'a =
  fun msg -> raise (Unexpected_error msg)

type valu_proof = valu * prop * unit
type term_proof = term * prop * unit

let rec type_check_valu : valu -> prop -> valu_proof = fun v c ->
  let r =
    match (Norm.repr v).elt with
    | LAbs(ao,b)  -> assert false
    | Cons(c,v)   -> assert false
    | Reco(m)     -> assert false
    | Scis        -> assert false
    | VTyp(v,a)   -> assert false
    | VLam(b)     -> assert false
    | VWit(t,a,b) -> assert false
    (* Constructors that cannot appear in user-defined terms. *)
    | UWit(_,_)   -> unexpected "∀-witness during typing..."
    | EWit(_,_)   -> unexpected "∃-witness during typing..."
    | UVar(_)     -> unexpected "unification variable during typing..."
    | Vari(_)     -> unexpected "Free variable during typing..."
    | HApp(_,_)   -> unexpected "Higher-order application during typing..."
    | Dumm        -> unexpected "Dummy value during typing..."
    | ITag(_)     -> unexpected "Tag during typing..."
  in
  (v, c, r)

and type_check_term : term -> prop -> term_proof = fun t c ->
  let r =
    match (Norm.repr t).elt with
    | Valu(v)     -> assert false
    | Appl(t,u)   -> assert false
    | MAbs(ao,b)  -> assert false
    | Name(pi,t)  -> assert false
    | Proj(v,l)   -> assert false
    | Case(v,m)   -> assert false
    | FixY(t,v)   -> assert false
    | TTyp(t,a)   -> assert false
    | TLam(b)     -> assert false
    (* Constructors that cannot appear in user-defined terms. *)
    | UWit(_,_)   -> unexpected "∀-witness during typing..."
    | EWit(_,_)   -> unexpected "∃-witness during typing..."
    | UVar(_)     -> unexpected "unification variable during typing..."
    | Vari(_)     -> unexpected "Free variable during typing..."
    | HApp(_,_)   -> unexpected "Higher-order application during typing..."
    | Dumm        -> unexpected "Dummy value during typing..."
    | ITag(_)     -> unexpected "Tag during typing..."
  in
  (t, c, r)

