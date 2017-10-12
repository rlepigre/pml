(** Function to retreive information from expression *)

open Extra
open Bindlib
open Eq
open Sorts
open Pos
open Ast
open Compare
open Output

type alist =
  | Nil  : alist
  | Cons : 'a ex * 'a box * alist -> alist

let assq_chrono = Chrono.create "assq"

let assq : type a. a ex -> alist -> a box = fun e l ->
  let rec fn : alist -> a box = fun l ->
    match l with
    | Nil -> raise Not_found
    | Cons(f,r,l) -> match e === f with Eq -> r | NEq -> fn l
  in
  Chrono.add_time assq_chrono fn l

exception NotClosed (* raised for ITag *)

(* a mapper may raise the exception Default *)
type recall = { recall : 'a. 'a ex loc -> 'a box }
type map = { map : 'a. recall -> 'a ex loc -> 'a box }
let defmap = { map = (fun { recall } x ->
                 let res = recall x in
                 if is_closed res then box x else res ) }

let (lift, lift_cond) =
  let rec lift_cond ?adone c =
    let adone = match adone with None -> ref Nil | Some a -> a in
    let res =
      match c with
      | Equiv(t,b,u) -> equiv (lift ~adone t) b (lift ~adone u)
      | Posit(o)     -> posit (lift ~adone o)
      | NoBox(v)     -> nobox (lift ~adone v)
    in
    if is_closed res then box c else res

  and lift : type a. ?map:map -> ?adone:alist ref -> a ex loc -> a box
  = fun ?(map=defmap) ?adone e ->
    let adone = match adone with None -> ref Nil | Some a -> a in
    let rec lift : type a. a ex loc -> a box = fun e ->
      let e = Norm.whnf e in
      try assq e.elt !adone with Not_found ->
        let recall : type a. a ex loc -> a box = fun e ->
          match e.elt with
            | HDef(_,_)   -> box e (* Assumed closed *)
            | HApp(s,f,a) -> happ e.pos s (lift f) (lift a)
            | HFun(a,b,f) -> hfun e.pos a b (bndr_name f)
                                  (fun x -> lift (bndr_subst f (mk_free a x)))
            | UWit(s,t,f) -> box e
            | EWit(s,t,f) -> box e
            | UVar(_,_)   -> box e
            | ITag(_,_)   -> box e
            | Goal(_,_)   -> box e

            | Func(a,b)   -> func e.pos (lift a) (lift b)
            | Prod(m)     -> prod e.pos (A.map (fun (p,a) -> (p, lift a)) m)
            | DSum(m)     -> dsum e.pos (A.map (fun (p,a) -> (p, lift a)) m)
            | Univ(s,f)   -> univ e.pos (bndr_name f) s
                                  (fun x -> lift (bndr_subst f (mk_free s x)))
            | Exis(s,f)   -> exis e.pos (bndr_name f) s
                                  (fun x -> lift (bndr_subst f (mk_free s x)))
            | FixM(o,f)   -> fixm e.pos (lift o) (bndr_name f)
                                  (fun x -> lift (bndr_subst f (mk_free P x)))
            | FixN(o,f)   -> fixn e.pos (lift o) (bndr_name f)
                                  (fun x -> lift (bndr_subst f (mk_free P x)))
            | Memb(t,a)   -> memb e.pos (lift t) (lift a)
            | Rest(a,c)   -> rest e.pos (lift a) (lift_cond ~adone c)
            | Impl(c,a)   -> impl e.pos (lift_cond ~adone c) (lift a)

            | VWit(_,_)   -> box e
            | LAbs(a,f)   -> labs e.pos (Option.map lift a) (bndr_name f)
                                  (fun x -> lift (bndr_subst f (mk_free V x)))
            | Cons(c,v)   -> cons e.pos c (lift v)
            | Reco(m)     -> reco e.pos (A.map (fun (p,v) -> (p, lift v)) m)
            | Scis        -> box e
            | VDef(_)     -> box e

            | Coer(t,e,a) -> coer e.pos t (lift e) (lift a)
            | Such(t,d,r) -> let sv =
                               match r.opt_var with
                               | SV_None    -> sv_none
                               | SV_Valu(v) -> sv_valu (lift v)
                               | SV_Stac(s) -> sv_stac (lift s)
                             in
                             let rec aux : type a b. (a, prop * b ex loc) bseq
                                 -> (a, prop * b ex loc) fseq =
                               fun b ->
                                 match b with
                                 | BLast(s,b) ->
                                     let x = binder_name b in
                                     let f x =
                                       let (p,e) = subst b (mk_free s x) in
                                       box_pair (lift p) (lift e)
                                     in
                                     FLast(s, Pos.none x, f)
                                 | BMore(s,b) ->
                                     let x = binder_name b in
                                     let f x = aux (subst b (mk_free s x)) in
                                     FMore(s, Pos.none x, f)
                             in
                             such e.pos t d sv (aux r.binder)

            | Valu(v)     -> valu e.pos (lift v)
            | Appl(t,u)   -> appl e.pos (lift t) (lift u)
            | MAbs(f)     -> mabs e.pos (bndr_name f)
                                  (fun x -> lift (bndr_subst f (mk_free S x)))
            | Name(s,t)   -> name e.pos (lift s) (lift t)
            | Proj(v,l)   -> proj e.pos (lift v) l
            | Case(v,m)   -> let fn (p,f) =
                               let fn x = lift (bndr_subst f (mk_free V x)) in
                               (p, bndr_name f, fn)
                             in
                             case e.pos (lift v) (A.map fn m)
            | FixY(f,v)   -> fixy e.pos (bndr_name f)
                               (fun x -> lift (bndr_subst f (mk_free V x)))
                               (lift v)
            | Prnt(s)     -> prnt e.pos s

            | Epsi        -> box e
            | Push(v,s)   -> push e.pos (lift v) (lift s)
            | Fram(t,s)   -> fram e.pos (lift t) (lift s)
            | SWit(f,a)   -> box e

            | Conv        -> box e
            | Succ(o)     -> succ e.pos (lift o)
            | OWMu(_,_)   -> box e
            | OWNu(_,_)   -> box e
            | OSch(_,_)   -> box e
            | Vari(_,x)   -> vari e.pos x
            | Dumm        -> box e
        in
        let res = map.map { recall } e in
        adone := Cons(e.elt,res,!adone);
        res
      in lift e
  in (lift, lift_cond)

type ('a, 'b) mbndr = ('a ex, 'b ex loc) mbinder

exception Found_index of int

let is_wit : type a. a ex loc -> bool = fun e -> match e.elt with
  | VWit _ -> true
  | OWMu _ -> true
  | OWNu _ -> true
  | UWit _ | EWit _ -> true
  | _ -> false

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
    | HDef(_,_)   -> acc
    | HApp(_,f,a) -> owits (owits acc f) a
    | HFun(_,_,f) -> owits acc (bndr_subst f Dumm)
    | UWit(_,s,_) ->
        begin
          match s with
          | O -> if is_in e acc then acc else e :: acc
          | _ -> acc
        end
    | EWit(_,s,_) ->
        begin
          match s with
          | O -> if is_in e acc then acc else e :: acc
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

    | VWit(_,_)   -> acc
    | LAbs(_,f)   -> owits acc (bndr_subst f Dumm)
    | Cons(_,v)   -> owits acc v
    | Reco(m)     -> A.fold (fun _ (_,v) acc -> owits acc v) m acc
    | Scis        -> acc
    | VDef(_)     -> acc

    | Valu(v)     -> owits acc v
    | Appl(t,u)   -> owits (owits acc t) u
    | MAbs(f)     -> owits acc (bndr_subst f Dumm)
    | Name(s,t)   -> owits (owits acc s) t
    | Proj(v,_)   -> owits acc v
    | Case(v,m)   -> let fn _ (_,f) acc = owits acc (bndr_subst f Dumm) in
                     A.fold fn m (owits acc v)
    | FixY(f,v)   -> owits (owits acc (bndr_subst f Dumm)) v
    | Prnt(_)     -> acc

    | Coer(_,e,_) -> owits acc e
    | Such(_,_,b) -> owits acc (bseq_dummy b.binder)

    | Epsi        -> acc
    | Push(v,s)   -> owits (owits acc v) s
    | Fram(t,s)   -> owits (owits acc t) s
    | SWit(_,_)   -> acc

    | Conv        -> acc
    | Succ(o)     -> owits acc o
    | OWMu(_,_)   -> if is_in e acc then acc else e :: acc
    | OWNu(_,_)   -> if is_in e acc then acc else e :: acc
    | OSch(_,_)   -> if is_in e acc then acc else e :: acc

    | Vari _      -> assert false
    | Dumm        -> acc
  in
  (* The ordinals to be bound. *)
  let owits = owits [] e in
  let os = Array.of_list owits in
  let arity = Array.length os in
  (* Name for the corresponding variables. *)
  let xs = Array.init arity (Printf.sprintf "o%i") in
  (* The variables themselves. *)
  let xs = new_mvar (mk_free O) xs in
  (* Binding function. *)
  let bind_all : type a. a ex loc -> a box =
    let map : type a. recall -> a ex loc -> a box = fun { recall } e ->
      let var_of_ordi_wit : type a.a sort -> a ex loc -> a box = fun s o ->
        match s with
        | O ->
           begin
             try
               for i = 0 to arity - 1 do
                 if eq_expr ~strict:true os.(i) o
                 then raise (Found_index(i))
               done;
               raise Not_found
             with Found_index(i) -> (vari o.pos xs.(i) : o box)
           end
        | _ -> raise Not_found
      in
      match e.elt with
      | UWit(_,s,_) -> (try var_of_ordi_wit s e with Not_found -> box e)
      | EWit(_,s,_) -> (try var_of_ordi_wit s e with Not_found -> box e)
      | OWMu(_,_)   -> (try var_of_ordi_wit O e with Not_found -> box e)
      | OWNu(_,_)   -> (try var_of_ordi_wit O e with Not_found -> box e)
      | OSch(_,_)   -> (try var_of_ordi_wit O e with Not_found -> box e)
      | _           -> recall e
    in
    fun e -> lift ~map:{map} e
  in
  (* Building the actual binder. *)
  let b = bind_mvar xs (bind_all e) in
  (unbox b, os)

let bind2_ordinals
    : p ex loc -> p ex loc -> (o ex, p ex loc * p ex loc) mbinder * ordi array
  = fun e1 e2 ->
  let m = A.singleton "1" (None, e1) in
  let m = A.add "2" (None, e2) m in
  let e = Pos.none (Prod m) in
  let (b, os) = bind_ordinals e in
  let names = mbinder_names b in
  let fn xs =
    match (msubst b xs).elt with
    | Prod m ->
       begin
         try  (snd (A.find "1" m), snd (A.find "2" m))
         with Not_found -> assert false
       end
    | _ -> assert false
  in
  (mbinder_from_fun names fn, os)

type occ = Pos | Neg | Any

let neg = function
  | Pos -> Neg
  | Neg | Any -> Any

let bind_spos_ordinals
    : p ex loc -> (o, p) mbndr * ordi array = fun e ->
  let vars = ref [] in
  let new_ord () =
    let v = new_var (mk_free O) "o" in
    vars := v::!vars;
    box_apply Pos.none (box_of_var v)
  in
  let assoc = ref [] in
  let rec search_ord o =
    let o = Norm.whnf o in
    match o.elt with
    | Succ o -> succ None (search_ord o)
    | _ ->
    try
      let (_,v) = List.find (fun (o',_) -> eq_expr ~strict:true o o') !assoc in
      v
    with Not_found ->
      let v = new_ord () in
      assoc := (o,v) :: !assoc;
      v
  in
  let rec bind_all : occ -> p ex loc -> p box = fun o e ->
    let ba = bind_all o in
    let e = Norm.whnf e in
    let adone = ref Nil in
    let res = match e.elt with
      (*| _ when o = Any -> lift ~adone e*)
    | HDef(_,e)   -> ba e.expr_def
    | Func(a,b)   -> func e.pos (bind_all (neg o) a) (ba b)
    | Prod(m)     -> prod e.pos (A.map (fun (p,a) -> (p, ba a)) m)
    | DSum(m)     -> dsum e.pos (A.map (fun (p,a) -> (p, ba a)) m)
    | Univ(s,f)   -> univ e.pos (bndr_name f) s
                       (fun x -> ba (bndr_subst f (mk_free s x)))
    | Exis(s,f)   -> exis e.pos (bndr_name f) s
                       (fun x -> ba (bndr_subst f (mk_free s x)))
    | FixM({ elt = Conv},f) when o = Neg ->
       fixm e.pos (new_ord ()) (bndr_name f)
            (fun x -> ba (bndr_subst f (mk_free P x)))
    | FixN({ elt = Conv},f) when o = Pos ->
       fixn e.pos (new_ord ()) (bndr_name f)
            (fun x -> ba (bndr_subst f (mk_free P x)))
    | FixM(o1,f) when (Norm.whnf o1).elt <> Conv ->
       fixm e.pos (search_ord o1) (bndr_name f)
            (fun x -> ba (bndr_subst f (mk_free P x)))
    | FixN(o1,f) when (Norm.whnf o1).elt <> Conv ->
       fixn e.pos (search_ord o1) (bndr_name f)
            (fun x -> ba (bndr_subst f (mk_free P x)))
    | Memb(t,a)   -> memb e.pos (lift ~adone t) (ba a)
    | Rest(a,c)   -> rest e.pos (ba a) (lift_cond ~adone c)
    | Impl(c,a)   -> impl e.pos (lift_cond ~adone c) (ba a)

    | _        -> lift ~adone e
    in
    let res = if is_closed res then box e else res in
    res
  in
  let e = bind_all Pos e in
  let vars = Array.of_list !vars in
  let b = bind_mvar vars e in
  let os = Array.make (Array.length vars) (Pos.none Conv) in
  (unbox b, os)
