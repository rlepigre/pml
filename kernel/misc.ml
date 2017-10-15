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

type apair =
  | P : 'a sort * 'a ex loc -> apair

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
type recall = { recall : 'a. 'a ex loc -> 'a box;
                default : 'a. 'a ex loc -> 'a box}
type mapper = { mapper : 'a. recall -> 'a ex loc -> 'a box }
let defmapper = { mapper = (fun { default } x ->
                    let res = default x in
                    if is_closed res then box x else res ) }

let map : type a. ?mapper:mapper -> ?adone:alist ref -> a ex loc -> a box
  = fun ?(mapper=defmapper) ?adone e ->
    let adone = match adone with None -> ref Nil | Some a -> a in
    let rec map_cond ?adone c =
      match c with
      | Equiv(t,b,u) -> equiv (map t) b (map u)
      | Posit(o)     -> posit (map o)
      | NoBox(v)     -> nobox (map v)

    and map : type a. a ex loc -> a box = fun e ->
      let e = Norm.whnf e in
      try assq e.elt !adone with Not_found ->
        let default : type a. a ex loc -> a box = fun e ->
          match e.elt with
            | HDef(_,_)   -> box e (* Assumed closed *)
            | HApp(s,f,a) -> happ e.pos s (map f) (map a)
            | HFun(a,b,f) -> hfun e.pos a b (bndr_name f)
                                  (fun x -> map (bndr_subst f (mk_free a x)))
            | UWit(s,t,f) -> box e
            | EWit(s,t,f) -> box e
            | UVar(_,_)   -> box e
            | ITag(_,_)   -> box e
            | Goal(_,_)   -> box e

            | Func(a,b)   -> func e.pos (map a) (map b)
            | Prod(m)     -> prod e.pos (A.map (fun (p,a) -> (p, map a)) m)
            | DSum(m)     -> dsum e.pos (A.map (fun (p,a) -> (p, map a)) m)
            | Univ(s,f)   -> univ e.pos (bndr_name f) s
                                  (fun x -> map (bndr_subst f (mk_free s x)))
            | Exis(s,f)   -> exis e.pos (bndr_name f) s
                                  (fun x -> map (bndr_subst f (mk_free s x)))
            | FixM(o,f)   -> fixm e.pos (map o) (bndr_name f)
                                  (fun x -> map (bndr_subst f (mk_free P x)))
            | FixN(o,f)   -> fixn e.pos (map o) (bndr_name f)
                                  (fun x -> map (bndr_subst f (mk_free P x)))
            | Memb(t,a)   -> memb e.pos (map t) (map a)
            | Rest(a,c)   -> rest e.pos (map a) (map_cond ~adone c)
            | Impl(c,a)   -> impl e.pos (map_cond ~adone c) (map a)

            | VWit(_,_)   -> box e
            | LAbs(a,f)   -> labs e.pos (Option.map map a) (bndr_name f)
                                  (fun x -> map (bndr_subst f (mk_free V x)))
            | Cons(c,v)   -> cons e.pos c (map v)
            | Reco(m)     -> reco e.pos (A.map (fun (p,v) -> (p, map v)) m)
            | Scis        -> box e
            | VDef(_)     -> box e

            | Coer(t,e,a) -> coer e.pos t (map e) (map a)
            | Such(t,d,r) -> let sv =
                               match r.opt_var with
                               | SV_None    -> sv_none
                               | SV_Valu(v) -> sv_valu (map v)
                               | SV_Stac(s) -> sv_stac (map s)
                             in
                             let rec aux : type a b. (a, prop * b ex loc) bseq
                                 -> (a, prop * b ex loc) fseq =
                               fun b ->
                                 match b with
                                 | BLast(s,b) ->
                                     let x = binder_name b in
                                     let f x =
                                       let (p,e) = subst b (mk_free s x) in
                                       box_pair (map p) (map e)
                                     in
                                     FLast(s, Pos.none x, f)
                                 | BMore(s,b) ->
                                     let x = binder_name b in
                                     let f x = aux (subst b (mk_free s x)) in
                                     FMore(s, Pos.none x, f)
                             in
                             such e.pos t d sv (aux r.binder)

            | Valu(v)     -> valu e.pos (map v)
            | Appl(t,u)   -> appl e.pos (map t) (map u)
            | MAbs(f)     -> mabs e.pos (bndr_name f)
                                  (fun x -> map (bndr_subst f (mk_free S x)))
            | Name(s,t)   -> name e.pos (map s) (map t)
            | Proj(v,l)   -> proj e.pos (map v) l
            | Case(v,m)   -> let fn (p,f) =
                               let fn x = map (bndr_subst f (mk_free V x)) in
                               (p, bndr_name f, fn)
                             in
                             case e.pos (map v) (A.map fn m)
            | FixY(f,v)   -> fixy e.pos (bndr_name f)
                               (fun x -> map (bndr_subst f (mk_free V x)))
                               (map v)
            | Prnt(s)     -> prnt e.pos s

            | Epsi        -> box e
            | Push(v,s)   -> push e.pos (map v) (map s)
            | Fram(t,s)   -> fram e.pos (map t) (map s)
            | SWit(f,a)   -> box e

            | Conv        -> box e
            | Succ(o)     -> succ e.pos (map o)
            | OWMu(_,_)   -> box e
            | OWNu(_,_)   -> box e
            | OSch(_,_)   -> box e
            | Vari(_,x)   -> vari e.pos x
            | Dumm        -> box e

            | VPtr _      -> box e (* FIXME: CHECK *)
            | TPtr _      -> box e (* FIXME: CHECK *)
        in
        let res = mapper.mapper { recall = map; default } e in
        adone := Cons(e.elt,res,!adone);
        res
      in map e

let lift : type a. a ex loc -> a box = fun e -> map e

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
  let bind_all : type a. a ex loc -> a box =
    let mapper : type a. recall -> a ex loc -> a box = fun { default } e ->
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
        | _ -> default o
      in
      match e.elt with
      | UWit(_,s,_) -> var_of_ordi_wit s e
      | EWit(_,s,_) -> var_of_ordi_wit s e
      | OWMu(_,_)   -> var_of_ordi_wit O e
      | OWNu(_,_)   -> var_of_ordi_wit O e
      | OSch(_,_)   -> var_of_ordi_wit O e
      | _           -> default e
    in
    fun e -> map ~mapper:{mapper} e
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
  let rec bind_all : type p. occ -> p ex loc -> p box = fun o e ->
    let mapper : type p. recall -> p ex loc -> p box =
    fun { recall; default } e ->
      match e.elt with
      | HDef(_,e)   -> recall e.expr_def
      | Func(a,b)   -> func e.pos (bind_all (neg o) a) (recall b)
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

type ('a, 'b) closure =
  (v ex, (t ex, ('a, 'b) bndr) mbinder) mbinder
  * v ex loc array
  * t ex loc array

let make_closure
    : type a b. a sort -> (a, b) bndr -> (a, b) closure
  = fun s b0 ->
    if binder_closed (snd b0) then
      let b0 = unbox (bind_mvar [||] (bind_mvar [||] (box b0))) in
      (b0, [||], [||])
    else
    let vl : v ex loc list ref = ref [] in
    let tl : t ex loc list ref = ref [] in
    let vv = ref [] in
    let tv = ref [] in
    let b = vbind (mk_free s) (bndr_name b0).elt (fun x ->
      let x = mk_free s x in
      let b = bndr_subst b0 x in
      let mapper : type a. recall -> a ex loc -> a box = fun {default} e ->
        let s, e = sort e in
        (* FIXME: this is quadratic !!! *)
        let e' = lift e in
        match is_closed e', s with
        | true, V ->
           let v = new_var (mk_free V) "v" in
           vl := e :: !vl;
           vv := v :: !vv;
           box_apply Pos.none (box_of_var v)
        | true, T ->
           let v = new_var (mk_free T) "v" in
           tl := e :: !tl;
           tv := v :: !tv;
           box_apply Pos.none (box_of_var v)
        | _ -> default e
      in
      map ~mapper:{mapper} b)
    in
    let tl = Array.of_list !tl in
    let vl = Array.of_list !vl in
    let tv = Array.of_list !tv in
    let vv = Array.of_list !vv in
    let b = box_pair (box (fst b0)) b in
    (unbox (bind_mvar vv (bind_mvar tv b)), vl, tl)
