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

let rec lift : type a. a ex loc -> a box = fun e ->
  let lift_cond c =
    match c with
    | Equiv(t,b,u) -> equiv (lift t) b (lift u)
    | Posit(o)     -> posit (lift o)
    | NoBox(v)     -> nobox (lift v)
  in
  let lift_schema { sch_index ; sch_posit ; sch_relat ; sch_judge } =
    let fn sch_judg = { sch_index ; sch_posit ; sch_relat ; sch_judge } in
    let gn x =
      let (t, a) = msubst sch_judge (Array.map mk_free x) in
      box_pair (lift t) (lift a)
    in
    box_apply fn (mvbind mk_free (mbinder_names sch_judge) gn)
  in
  match (Norm.whnf e).elt with
  | HDef(_,_)   -> box e (* Assumed closed *)
  | HApp(s,f,a) -> happ e.pos s (lift f) (lift a)
  | HFun(a,b,f) -> hfun e.pos a b (bndr_name f)
                     (fun x -> lift (bndr_subst f (mk_free x)))
  | UWit(s,t,f) -> uwit e.pos (lift t) (bndr_name f) s
                     (fun x -> lift (bndr_subst f (mk_free x)))
  | EWit(s,t,f) -> ewit e.pos (lift t) (bndr_name f) s
                     (fun x -> lift (bndr_subst f (mk_free x)))
  | UVar(_,_)   -> box e
  | ITag(_,_)   -> box e
  | Goal(_,_)   -> box e

  | Func(a,b)   -> func e.pos (lift a) (lift b)
  | Prod(m)     -> prod e.pos (A.map (fun (p,a) -> (p, lift a)) m)
  | DSum(m)     -> dsum e.pos (A.map (fun (p,a) -> (p, lift a)) m)
  | Univ(s,f)   -> univ e.pos (bndr_name f) s
                     (fun x -> lift (bndr_subst f (mk_free x)))
  | Exis(s,f)   -> exis e.pos (bndr_name f) s
                     (fun x -> lift (bndr_subst f (mk_free x)))
  | FixM(o,f)   -> fixm e.pos (lift o) (bndr_name f)
                     (fun x -> lift (bndr_subst f (mk_free x)))
  | FixN(o,f)   -> fixn e.pos (lift o) (bndr_name f)
                     (fun x -> lift (bndr_subst f (mk_free x)))
  | Memb(t,a)   -> memb e.pos (lift t) (lift a)
  | Rest(a,c)   -> rest e.pos (lift a) (lift_cond c)
  | Impl(c,a)   -> impl e.pos (lift_cond c) (lift a)

  | VWit(t,a,b) -> vdwit e.pos (bndr_name t)
                     (fun x -> lift (bndr_subst t (mk_free x)))
                     (fun x -> lift (bndr_subst a (mk_free x)))
                     (lift b)
  | LAbs(a,f)   -> labs e.pos (Option.map lift a) (bndr_name f)
                     (fun x -> lift (bndr_subst f (mk_free x)))
  | Cons(c,v)   -> cons e.pos c (lift v)
  | Reco(m)     -> reco e.pos (A.map (fun (p,v) -> (p, lift v)) m)
  | Scis        -> box e
  | VDef(_)     -> box e
  | VTyp(v,a)   -> vtyp e.pos (lift v) (lift a)
  | VLam(s,f)   -> vlam e.pos (bndr_name f) s
                     (fun x -> lift (bndr_subst f (mk_free x)))

  | Valu(v)     -> valu e.pos (lift v)
  | Appl(t,u)   -> appl e.pos (lift t) (lift u)
  | MAbs(f)     -> mabs e.pos (bndr_name f)
                     (fun x -> lift (bndr_subst f (mk_free x)))
  | Name(s,t)   -> name e.pos (lift s) (lift t)
  | Proj(v,l)   -> proj e.pos (lift v) l
  | Case(v,m)   -> let fn (p,f) =
                     let fn x = lift (bndr_subst f (mk_free x)) in
                     (p, bndr_name f, fn)
                   in
                   case e.pos (lift v) (A.map fn m)
  | FixY(t,v)   -> fixy e.pos (lift t) (lift v)
  | TTyp(t,a)   -> ttyp e.pos (lift t) (lift a)
  | TLam(s,f)   -> tlam e.pos (bndr_name f) s
                     (fun x -> lift (bndr_subst f (mk_free x)))

  | Epsi        -> box e
  | Push(v,s)   -> push e.pos (lift v) (lift s)
  | Fram(t,s)   -> fram e.pos (lift t) (lift s)
  | SWit(f,a)   -> swit e.pos (bndr_name f)
                     (fun x -> lift (bndr_subst f (mk_free x)))
                     (lift a)

  | Conv        -> box e
  | Succ(o)     -> succ e.pos (lift o)
  | OWit(o,i,s) -> owit e.pos (lift o) i (lift_schema s)

  | Vari(x)     -> vari e.pos x
  | Dumm        -> box e

type ('a, 'b) mbndr = ('a ex, 'b ex loc) mbinder

exception Found_index of int

let bind_ordinals : type a. a ex loc -> (o, a) mbndr * ordi array = fun e ->
  (* Compute the list of all the surface ordinal witnesses. *)
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
          | _ -> acc
        end
    | EWit(s,t,a) ->
        begin
          match s with
          | O -> if List.memq e acc then e :: acc else acc
          | _ -> acc
        end
    | UVar(_,_)   -> acc
    | ITag(_,_)   -> acc
    | Goal(_,_)   -> acc

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

    | VWit(_,_,_) -> acc
    | LAbs(_,f)   -> owits acc (bndr_subst f Dumm)
    | Cons(_,v)   -> owits acc v
    | Reco(m)     -> A.fold (fun _ (_,v) acc -> owits acc v) m acc
    | Scis        -> acc
    | VDef(_)     -> acc
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

    | Epsi        -> acc
    | Push(v,s)   -> owits (owits acc v) s
    | Fram(t,s)   -> owits (owits acc t) s
    | SWit(_,_)   -> acc

    | Conv        -> acc
    | Succ(o)     -> owits acc o
    | OWit(_)     -> if List.memq e acc then e :: acc else acc

    | Vari _      -> acc
    | Dumm        -> acc
  in
  (* The ordinals to be bound. *)
  let os = Array.of_list (owits [] e) in
  let arity = Array.length os in
  (* Name for the corresponding variables. *)
  let xs = Array.init arity (Printf.sprintf "o%i") in
  (* The variables themselves. *)
  let xs = new_mvar mk_free xs in
  (* Binding function. *)
  let rec bind_all : type a. a ex loc -> a box = fun e ->
    let bind_all_cond c =
      match c with
      | Equiv(t,b,u) -> equiv (bind_all t) b (bind_all u)
      | Posit(o)     -> posit (bind_all o)
      | NoBox(v)     -> nobox (bind_all v)
    in
    let var_of_ordi_wit o =
      try
        for i = 0 to arity - 1 do
          if os.(i) == o then raise (Found_index(i))
        done;
        lift o
      with Found_index(i) -> vari o.pos xs.(i)
    in
    match (Norm.whnf e).elt with
    | HDef(_,_)   -> box e (* Assumed closed *)
    | HApp(s,f,a) -> happ e.pos s (bind_all f) (bind_all a)
    | HFun(a,b,f) -> hfun e.pos a b (bndr_name f)
                       (fun x -> bind_all (bndr_subst f (mk_free x)))
    | UWit(s,_,_) ->
        begin
          match s with
          | O -> var_of_ordi_wit e
          | _ -> lift e
        end
    | EWit(s,_,_) ->
        begin
          match s with
          | O -> var_of_ordi_wit e
          | _ -> lift e
        end
    | UVar(_,_)   -> box e
    | ITag(_,_)   -> box e
    | Goal(_,_)   -> box e

    | Func(a,b)   -> func e.pos (bind_all a) (bind_all b)
    | Prod(m)     -> prod e.pos (A.map (fun (p,a) -> (p, bind_all a)) m)
    | DSum(m)     -> dsum e.pos (A.map (fun (p,a) -> (p, bind_all a)) m)
    | Univ(s,f)   -> univ e.pos (bndr_name f) s
                       (fun x -> bind_all (bndr_subst f (mk_free x)))
    | Exis(s,f)   -> exis e.pos (bndr_name f) s
                       (fun x -> bind_all (bndr_subst f (mk_free x)))
    | FixM(o,f)   -> fixm e.pos (bind_all o) (bndr_name f)
                       (fun x -> bind_all (bndr_subst f (mk_free x)))
    | FixN(o,f)   -> fixn e.pos (bind_all o) (bndr_name f)
                       (fun x -> bind_all (bndr_subst f (mk_free x)))
    | Memb(t,a)   -> memb e.pos (bind_all t) (bind_all a)
    | Rest(a,c)   -> rest e.pos (bind_all a) (bind_all_cond c)
    | Impl(c,a)   -> impl e.pos (bind_all_cond c) (bind_all a)

    | VWit(_,_,_) -> lift e
    | LAbs(a,f)   -> labs e.pos (Option.map bind_all a) (bndr_name f)
                       (fun x -> bind_all (bndr_subst f (mk_free x)))
    | Cons(c,v)   -> cons e.pos c (bind_all v)
    | Reco(m)     -> reco e.pos (A.map (fun (p,v) -> (p, bind_all v)) m)
    | Scis        -> box e
    | VDef(_)     -> box e
    | VTyp(v,a)   -> vtyp e.pos (bind_all v) (bind_all a)
    | VLam(s,f)   -> vlam e.pos (bndr_name f) s
                       (fun x -> bind_all (bndr_subst f (mk_free x)))

    | Valu(v)     -> valu e.pos (bind_all v)
    | Appl(t,u)   -> appl e.pos (bind_all t) (bind_all u)
    | MAbs(f)     -> mabs e.pos (bndr_name f)
                       (fun x -> bind_all (bndr_subst f (mk_free x)))
    | Name(s,t)   -> name e.pos (bind_all s) (bind_all t)
    | Proj(v,l)   -> proj e.pos (bind_all v) l
    | Case(v,m)   -> let fn (p,f) =
                       let fn x = bind_all (bndr_subst f (mk_free x)) in
                       (p, bndr_name f, fn)
                     in
                     case e.pos (bind_all v) (A.map fn m)
    | FixY(t,v)   -> fixy e.pos (bind_all t) (bind_all v)
    | TTyp(t,a)   -> ttyp e.pos (bind_all t) (bind_all a)
    | TLam(s,f)   -> tlam e.pos (bndr_name f) s
                       (fun x -> bind_all (bndr_subst f (mk_free x)))

    | Epsi        -> box e
    | Push(v,s)   -> push e.pos (bind_all v) (bind_all s)
    | Fram(t,s)   -> fram e.pos (bind_all t) (bind_all s)
    | SWit(_,_)   -> lift e

    | Conv        -> box e
    | Succ(o)     -> succ e.pos (bind_all o)
    | OWit(_)     -> var_of_ordi_wit e

    | Vari(x)     -> vari e.pos x
    | Dumm        -> box e
  in
  (* Building the actual binder. *)
  let b = bind_mvar xs (bind_all e) in
  (unbox b, os)
