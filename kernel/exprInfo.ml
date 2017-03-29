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
  | ITag(s,_)   -> (s,e)
  | Goal(s,_)   -> (s,e)

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

type ('a, 'b) mbndr = ('a ex loc, 'b ex loc) mbinder

let generalise : type a. a ex loc -> (o, a) mbndr * ordi array = fun e ->
  let rec owits : type a. ordi list -> a ex loc -> ordi list = fun acc e ->
    let from_cond acc c =
      match c with
      | Equiv(t,_,u) -> owits (owits acc t) u
      | Posit(o)     -> owits acc o
      | NoBox(v)     -> owits acc v
    in
    match (Norm.whnf e).elt with
    | HDef(_,_)   -> []
    | HApp(_,f,a) -> owits (owits acc f) a
    | HFun(_,_,f) -> owits acc (bndr_subst f Dumm)
    | UWit(s,t,a) ->
        begin
          match s with
          | O -> if List.memq e acc then e :: acc else acc
          | _ -> owits (owits acc t) (bndr_subst a Dumm)
        end
    | EWit(s,t,a) ->
        begin
          match s with
          | O -> if List.memq e acc then e :: acc else acc
          | _ -> owits (owits acc t) (bndr_subst a Dumm)
        end
    | UVar(_,_)   -> []
    | ITag(_,_)   -> []
    | Goal(_,_)   -> []

    | Func(a,b)   -> owits (owits acc a) b
    | Prod(m)     -> A.fold (fun _ (_,a) acc -> owits acc a) m acc
    | DSum(m)     -> A.fold (fun _ (_,a) acc -> owits acc a) m acc
    | Univ(_,f)   -> owits acc (bndr_subst f Dumm)
    | Exis(_,f)   -> owits acc (bndr_subst f Dumm)
    | FixM(o,f)   -> owits (owits acc o) (bndr_subst f Dumm)
    | FixN(o,f)   -> owits (owits acc o) (bndr_subst f Dumm)
    | Memb(t,a)   -> owits (owits acc t) a
    | Rest(a,c)   -> owits (from_cond acc c) a
    | Impl(c,a)   -> owits (from_cond acc c) a

    | VWit(t,a,b) -> owits (owits (owits acc
                       (bndr_subst t Dumm)) (bndr_subst a Dumm)) b
    | LAbs(_,f)   -> owits acc (bndr_subst f Dumm)
    | Cons(_,v)   -> owits acc v
    | Reco(m)     -> A.fold (fun _ (_,v) acc -> owits acc v) m acc
    | Scis        -> []
    | VDef(_)     -> []
    | VTyp(v,_)   -> owits acc v
    | VLam(_,f)   -> owits acc (bndr_subst f Dumm)

    | Valu(v)     -> owits acc v
    | Appl(t,u)   -> owits (owits acc t) u
    | MAbs(f)     -> owits acc (bndr_subst f Dumm)
    | Name(s,t)   -> owits (owits acc s) t
    | Proj(v,_)   -> owits acc v
    | Case(v,m)   -> let fn _ (_,f) acc = owits acc (bndr_subst f Dumm) in
                     A.fold fn m (owits acc v)
    | FixY(t,v)   -> owits (owits acc t) v
    | TTyp(t,_)   -> owits acc t
    | TLam(_,f)   -> owits acc (bndr_subst f Dumm)

    | Epsi        -> []
    | Push(v,s)   -> owits (owits acc v) s
    | Fram(t,s)   -> owits (owits acc t) s
    | SWit(f,a)   -> owits (owits acc (bndr_subst f Dumm)) a

    | Conv        -> []
    | Succ(o)     -> owits acc o
    | OWit(_)     -> if List.memq e acc then e :: acc else acc

    | Vari _      -> []
    | Dumm        -> []
  in
  let os = owits [] e in

  (* TODO *)
  ignore os;
  assert false
