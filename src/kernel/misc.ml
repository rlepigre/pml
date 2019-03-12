(** Function to retreive information from expression *)

open Extra
open Bindlib
open Sorts
open Pos
open Ast
open Mapper
open Compare

type apair =
  | P : 'a sort * 'a ex loc -> apair

exception NotClosed (* raised for ITag *)

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
      | NoBox(v)     -> owits acc v
    in
    match (Norm.whnf e).elt with
    | HDef(_,_)   -> acc
    | HApp(_,f,a) -> owits (owits acc f) a
    | HFun(s,_,f) -> owits acc (bndr_subst f (Dumm s))
    | UWit(w)     ->
        begin
          let (s,_,_) = !(w.valu) in
          match s with
          | O -> if is_in e acc then acc else e :: acc
          | _ -> acc
        end
    | EWit(w)     ->
        begin
          let (s,_,_) = !(w.valu) in
          match s with
          | O -> if is_in e acc then acc else e :: acc
          | _ -> acc
        end
    | UVar(_,_)   -> acc
    | ITag(_,_)   -> acc
    | Goal(_,_)   -> acc

    | Func(_,a,b) -> owits (owits acc a) b
    | Prod(m)     -> A.fold (fun _ (_,a) acc -> owits acc a) m acc
    | DSum(m)     -> A.fold (fun _ (_,a) acc -> owits acc a) m acc
    | Univ(s,f)   -> owits acc (bndr_subst f (Dumm s))
    | Exis(s,f)   -> owits acc (bndr_subst f (Dumm s))
    | FixM(o,f)   -> owits (owits acc o) (bndr_subst f (Dumm P))
    | FixN(o,f)   -> owits (owits acc o) (bndr_subst f (Dumm P))
    | Memb(t,a)   -> owits (owits acc t) a
    | Rest(a,c)   -> owits (from_cond acc c) a
    | Impl(c,a)   -> owits (from_cond acc c) a

    | VWit(_)     -> acc
    | LAbs(_,f)   -> owits acc (bndr_subst f (Dumm V))
    | Cons(_,v)   -> owits acc v
    | Reco(m)     -> A.fold (fun _ (_,v) acc -> owits acc v) m acc
    | Scis        -> acc
    | VDef(_)     -> acc

    | Valu(v)     -> owits acc v
    | Appl(t,u)   -> owits (owits acc t) u
    | FixY(_,f)   -> owits acc (bndr_subst f (Dumm T))
    | MAbs(f)     -> owits acc (bndr_subst f (Dumm S))
    | Name(s,t)   -> owits (owits acc s) t
    | Proj(v,_)   -> owits acc v
    | Case(v,m)   -> let fn _ (_,f) acc = owits acc (bndr_subst f (Dumm V)) in
                     A.fold fn m (owits acc v)
    | Prnt(_)     -> acc
    | Repl(t,u)   -> owits acc u
    | Delm(u)     -> owits acc u

    | Coer(_,e,_) -> owits acc e
    | Such(_,_,b) -> owits acc (bseq_dummy b.binder)
    | PSet(_,_,e) -> owits acc e

    | SWit(_)     -> acc

    | Conv        -> acc
    | Succ(o)     -> owits acc o
    | OWMu(_)     -> if is_in e acc then acc else e :: acc
    | OWNu(_)     -> if is_in e acc then acc else e :: acc
    | OSch(_)     -> if is_in e acc then acc else e :: acc

    | Vari _      -> assert false
    | Dumm _      -> acc
    | VPtr _      -> acc
    | TPtr _      -> acc
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
  let bind_all : type a. a ex loc -> a ebox =
    let mapper : type a. recall -> a ex loc -> a ebox = fun { default } e ->
      let var_of_ordi_wit : type a.a sort -> a ex loc -> a ebox = fun s o ->
        match s with
        | O ->
           begin
             try
               for i = 0 to arity - 1 do
                 if eq_expr os.(i) o
                 then raise (Found_index(i))
               done;
               raise Not_found
             with Found_index(i) -> (vari o.pos xs.(i) : o ebox)
           end
        | _ -> default o
      in
      match e.elt with
      | UWit(w) -> let (s,_,_) = !(w.valu) in var_of_ordi_wit s e
      | EWit(w) -> let (s,_,_) = !(w.valu) in var_of_ordi_wit s e
      | OWMu(_) -> var_of_ordi_wit O e
      | OWNu(_) -> var_of_ordi_wit O e
      | OSch(_) -> var_of_ordi_wit O e
      | _       -> default e
    in
    fun e -> map ~mapper:{mapper} e
  in
  (* Building the actual binder. *)
  let b = bind_mvar xs (bind_all e) in
  (unbox b, os)

let bind2_ordinals : p ex loc -> p ex loc
    -> (o ex, p ex loc * p ex loc) mbinder * ordi array = fun e1 e2 ->
  let m = A.singleton "1" (None, e1) in
  let m = A.add "2" (None, e2) m in
  let e = Pos.none (Prod m) in
  let (b, os) = bind_ordinals e in
  let names = mbinder_names b in
  let xs = new_mvar (mk_free O) names in
  let fn =
    match (msubst b (Array.map (mk_free O) xs)).elt with
    | Prod m ->
       begin
         try  box_pair (lift (snd (A.find "1" m))) (lift (snd (A.find "2" m)))
         with Not_found -> assert false
       end
    | _ -> assert false
  in
  (unbox (bind_mvar xs fn), os)

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
    box_apply Pos.none (box_var v)
  in
  let assoc = ref [] in
  let rec search_ord o =
    let o = Norm.whnf o in
    match o.elt with
    | Succ o -> succ None (search_ord o)
    | _ ->
    try
      let (_,v) = List.find (fun (o',_) -> eq_expr o o') !assoc in
      v
    with Not_found ->
      let v = new_ord () in
      assoc := (o,v) :: !assoc;
      v
  in
  let rec bind_all : type p. occ -> p ex loc -> p ebox = fun o e ->
    let mapper : type p. recall -> p ex loc -> p ebox =
    fun { recall; default } e ->
      match e.elt with
      | HDef(_,e)   -> recall e.expr_def
      | Func(t,a,b) -> func e.pos t (bind_all (neg o) a) (recall b)
      | FixM({ elt = Conv},f) when o = Neg ->
         fixm e.pos (new_ord ()) (bndr_name f)
              (fun x -> recall (bndr_subst f (mk_free P x)))
      | FixN({ elt = Conv},f) when o = Pos ->
         fixn e.pos (new_ord ()) (bndr_name f)
              (fun x -> recall (bndr_subst f (mk_free P x)))
      | FixM(o1,f) when (Norm.whnf o1).elt <> Conv ->
         fixm e.pos (search_ord o1) (bndr_name f)
              (fun x -> recall (bndr_subst f (mk_free P x)))
      | FixN(o1,f) when (Norm.whnf o1).elt <> Conv ->
         fixn e.pos (search_ord o1) (bndr_name f)
              (fun x -> recall (bndr_subst f (mk_free P x)))
      | _        -> default e
    in
    map ~mapper:{mapper} e
  in
  let e = bind_all Pos e in
  let vars = Array.of_list !vars in
  let b = bind_mvar vars e in
  let os = Array.make (Array.length vars) (Pos.none Conv) in
  (unbox b, os)

let box_closure: type a. a ex loc -> a ebox * t var array * v var array
                                     * t ex loc array * v ex loc array
  = fun e ->
    let vl : v ex loc list ref = ref [] in
    let tl : t ex loc list ref = ref [] in
    let vv = ref [] in
    let tv = ref [] in
    let mapper : type a. recall -> a ex loc -> a ebox = fun {default} e ->
      let s, e = sort e in
      let svl = !vl and stl = !tl and svv = !vv and stv = !tv in
      let e' = default e in
      match is_closed e', s with
      | true, V ->
         vl := svl; tl := stl; vv := svv; tv := stv;
         let v = new_var (mk_free V) "v" in
         vl := e :: !vl;
         vv := v :: !vv;
         box (Pos.none (mk_free V v))
      | true, T ->
         vl := svl; tl := stl; vv := svv; tv := stv;
         let v = new_var (mk_free T) "v" in
         tl := e :: !tl;
         tv := v :: !tv;
         box (Pos.none (mk_free T v))
      | _ -> e'
    in
    let e = map ~mapper:{mapper} e in
    let tl = Array.of_list !tl in
    let vl = Array.of_list !vl in
    let tv = Array.of_list !tv in
    let vv = Array.of_list !vv in
    (lift (unbox e),tv,vv,tl,vl)

type 'a closure =
  (v ex, (t ex, 'a) mbinder) mbinder * v ex loc array * t ex loc array


let make_closure : type a. a ex loc -> a ex loc closure = fun e ->
  let (e,tv,vv,tl,vl) = box_closure e in
  (unbox (bind_mvar vv (bind_mvar tv e)), vl, tl)

let make_bndr_closure
    : type a b. a sort -> (a, b) bndr -> (a, b) bndr closure
  = fun s b0 ->
    let (x,e) = unbind (snd b0) in
    let (e,tv,vv,tl,vl) = box_closure e in
    let b = bind_var x e in
    let b = box_pair (box (fst b0)) b in
    (unbox (bind_mvar vv (bind_mvar tv b)), vl, tl)

let closure_chrono = Chrono.create "closure"

let make_closure e =
  Chrono.add_time closure_chrono make_closure e
let make_bndr_closure s e =
  Chrono.add_time closure_chrono (make_bndr_closure s) e
