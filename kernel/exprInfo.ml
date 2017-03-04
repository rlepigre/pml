(** Function to retreive information from expression *)

open Bindlib
open Sorts
open Pos
open Ast
open Output

exception NotClosed (* raised for ITag *)

let rec sort : type a b. a ex loc ->  a sort * a ex loc= fun e ->
  let e = Norm.whnf e in
  match e.elt with
  | HDef(s,_)   -> (s, e)
  | HApp(d,u,v) -> let (F(_,s),_) = sort u in (s,e)
  | HFun(d,c,r) -> (F(d, c), e)
  | UWit(s,_,_) -> (s,e)
  | EWit(s,_,_) -> (s,e)
  | UVar(s,_)   -> (s,e)

  | Func _      -> (P,e)
  | Prod _      -> (P,e)
  | DSum _      -> (P,e)
  | Univ _      -> (P,e)
  | Exis _      -> (P,e)
  | FixM _      -> (P,e)
  | FixN _      -> (P,e)
  | Memb _      -> (P,e)
  | Rest _      -> (P,e)
  | Impl _      -> (P,e)

  | VWit _      -> (V,e)
  | LAbs _      -> (V,e)
  | Cons _      -> (V,e)
  | Reco _      -> (V,e)
  | Scis        -> (V,e)
  | VDef _      -> (V,e)
  | VTyp _      -> (V,e)
  | VLam _      -> (V,e)

  | Valu _      -> (T,e)
  | Appl _      -> (T,e)
  | MAbs _      -> (T,e)
  | Name _      -> (T,e)
  | Proj _      -> (T,e)
  | Case _      -> (T,e)
  | FixY _      -> (T,e)
  | TTyp _      -> (T,e)
  | TLam _      -> (T,e)

  | Epsi        -> (S,e)
  | Push _      -> (S,e)
  | Fram _      -> (S,e)
  | SWit _      -> (S,e)

  | Conv        -> (O,e)
  | Succ _      -> (O,e)
  | OWit _      -> (O,e)

  | Vari _      -> assert false
  | ITag _      -> raise NotClosed
  | Dumm        -> assert false

let isVal : type a.a ex loc -> v ex loc option = fun e ->
  match sort e with
  | (V,e)               -> Some e
  | (T,{ elt = Valu e}) -> Some e
  | _                   -> None

let isTerm : type a.a ex loc -> t ex loc option = fun e ->
  match sort e with
  | (V,e) -> Some (Pos.none (Valu e))
  | (T,e) -> Some e
  | _     -> None


(*
let rec term_has_type : term -> bool = fun t ->
  let t = Norm.whnf t in
  match t with
  | Appl(t,_) -> term_has_type t
  | (V,e)alu v -> valu_has_type v

and value_has_type
 *)
