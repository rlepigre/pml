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

let fake_bind :  type a. a ex loc -> (o, a) mbndr * ordi array = fun e ->
  let e = box e in
  let v = new_mvar (mk_free O) [||] in
  (unbox (bind_mvar v e), [||])

let bind_ordinals : type a. a ex loc -> (o, a) mbndr * ordi array = fun e ->
  (* Compute the list of all the surface ordinal witnesses. *)
  let rec owits : type a. ordi list -> a ex loc -> ordi list = fun acc e ->
    let from_cond acc c =
      match c with
      | Equiv(t,_,u) -> owits (owits acc t) u
      | NoBox(v)     -> owits acc v
    in
    let rec from_args : type a b. ordi list -> (a,b) fix_args -> ordi list =
      fun acc l ->
        match l with
        | Nil       -> acc
        | Cns(a, l) -> from_args (owits acc a) l
    in
    match (Norm.whnf e).elt with
    | HDef(_,_)   -> acc
    | HApp(_,f,a) -> owits (owits acc f) a
    | HFun(s,_,f) -> owits acc (bndr_term f)
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
    | Goal(_,_)   -> acc

    | Func(_,a,b,l)
                  -> owits (owits acc a) b
    | Prod(m)     -> A.fold (fun _ (_,a) acc -> owits acc a) m acc
    | DSum(m)     -> A.fold (fun _ (_,a) acc -> owits acc a) m acc
    | Univ(s,f)   -> owits acc (bndr_term f)
    | Exis(s,f)   -> owits acc (bndr_term f)
    | FixM(s,o,f,l)
                  -> from_args (owits (owits acc o) (bndr_term f)) l
    | FixN(s,o,f,l)
                  -> from_args (owits (owits acc o) (bndr_term f)) l
    | Memb(t,a)   -> owits (owits acc t) a
    | Rest(a,c)   -> owits (from_cond acc c) a
    | Impl(c,a)   -> owits (from_cond acc c) a

    | VWit(_)     -> acc
    | LAbs(_,f,_) -> owits acc (bndr_term f)
    | Cons(_,v)   -> owits acc v
    | Reco(m)     -> A.fold (fun _ (_,v) acc -> owits acc v) m acc
    | Scis        -> acc
    | VDef(_)     -> acc

    | Valu(v)     -> owits acc v
    | Appl(t,u,l) -> owits (owits acc t) u
    | FixY(f)     -> owits acc (bndr_term f)
    | MAbs(f)     -> owits acc (bndr_term f)
    | Name(s,t)   -> owits (owits acc s) t
    | Proj(v,_)   -> owits acc v
    | Case(v,m)   -> let fn _ (_,f) acc = owits acc (bndr_term f) in
                     A.fold fn m (owits acc v)
    | Prnt(_)     -> acc
    | Repl(t,u)   -> owits acc u
    | Delm(u)     -> owits acc u
    | Hint(_,u)   -> owits acc u

    | Coer(_,e,_) -> owits acc e
    | Such(_,_,b) -> owits acc (bseq_open b.binder)

    | SWit(_)     -> acc

    | Conv        -> acc
    | Succ(o)     -> owits acc o
    | OWMu(_)     -> if is_in e acc then acc else e :: acc
    | OWNu(_)     -> if is_in e acc then acc else e :: acc
    | OSch(_)     -> if is_in e acc then acc else e :: acc
    | ESch(s,_,w) -> begin
                       match s with
                       | O -> if is_in e acc then acc else e :: acc
                       | _ -> acc
                     end

    | Vari _      -> acc
    | VPtr _      -> acc
    | TPtr _      -> acc
    | ITag _      -> assert false
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

type slist =
  | Nil : slist
  | Cns : 'a sort * 'a ex loc * slist -> slist

let in_slist : type a. a ex loc -> slist -> bool = fun e l ->
  let (s, e) = sort e in
  let rec fn = function
    | Nil          -> false
    | Cns(s1,e1,l) ->
       match eq_sort s s1 with
       | Eq.Eq  -> eq_expr e e1 || fn l
       | Eq.NEq -> fn l
  in
  fn l

let len_slist : slist -> int =
  let rec fn acc = function
    | Nil        -> acc
    | Cns(_,_,l) -> fn (acc + 1) l
  in
  fn 0

type sassoc =
  | Nil : sassoc
  | Cns : 'a sort * 'a ex loc * 'a var * sassoc -> sassoc

let sassoc : type a. Equiv.pool -> a ex loc -> sassoc -> a var = fun po e l ->
  let (s, e) = sort e in
  let rec fn : sassoc -> a var = function
    | Nil          -> raise Not_found
    | Cns(s1,e1,v1,l) ->
       match eq_sort s s1 with
       | Eq.Eq  -> if Equiv.unif_expr po e e1 then v1 else fn l
       | Eq.NEq -> fn l
  in
  fn l

let rec mk_sassoc : slist -> sassoc = function
  | Nil        -> Nil
  | Cns(s,e,l) -> let v = new_var (mk_free s) "a" in Cns(s,e,v,mk_sassoc l)


let bind_params : Equiv.pool -> p ex loc -> sbndr box * slist = fun po e ->
  (* Compute the list of all the surface ordinal witnesses. *)

  let rec params : type a. slist -> a ex loc -> slist = fun acc e ->
    let from_cond acc c =
      match c with
      | Equiv(t,_,u) -> params (params acc t) u
      | NoBox(v)     -> params acc v
    in
    let rec from_args : type a b. slist -> (a,b) fix_args -> slist =
      fun acc l ->
        match l with
        | Nil       -> acc
        | Cns(a, l) -> let acc =
                         if in_slist a acc then acc else
                           let (s,a) = sort a in
                           Cns(s,a,acc)
                       in
                       from_args (params acc a) l
    in
    match (Norm.whnf e).elt with
    | HDef(_,_)   -> acc
    | HApp(_,f,a) -> params (params acc f) a
    | HFun(s,_,f) -> let (_,t) = bndr_open f in params acc t
    | UWit(w)     -> acc
    | EWit(w)     -> acc
    | UVar(_,_)   -> acc
    | Goal(_,_)   -> acc

    | Func(_,a,b,l)
                  -> params (params acc a) b
    | Prod(m)     -> A.fold (fun _ (_,a) acc -> params acc a) m acc
    | DSum(m)     -> A.fold (fun _ (_,a) acc -> params acc a) m acc
    | Univ(s,f)   -> let (_,t) = bndr_open f in params acc t
    | Exis(s,f)   -> let (_,t) = bndr_open f in params acc t
    | FixM(s,o,f,l)
                  -> let (_,t) = bndr_open f in
                     from_args (params (params acc o) t) l
    | FixN(s,o,f,l)
                  -> let (_,t) = bndr_open f in
                     from_args (params (params acc o) t) l
    | Memb(t,a)   -> params (params acc t) a
    | Rest(a,c)   -> params (from_cond acc c) a
    | Impl(c,a)   -> params (from_cond acc c) a

    | VWit(_)     -> acc
    | LAbs(_,f,_) -> let (_,t) = bndr_open f in params acc t
    | Cons(_,v)   -> params acc v
    | Reco(m)     -> A.fold (fun _ (_,v) acc -> params acc v) m acc
    | Scis        -> acc
    | VDef(_)     -> acc

    | Valu(v)     -> params acc v
    | Appl(t,u,_) -> params (params acc t) u
    | FixY(f)     -> let (_,t) = bndr_open f in params acc t
    | MAbs(f)     -> let (_,t) = bndr_open f in params acc t
    | Name(s,t)   -> params (params acc s) t
    | Proj(v,_)   -> params acc v
    | Case(v,m)   -> let fn _ (_,f) acc = params acc (bndr_term f) in
                     A.fold fn m (params acc v)
    | Prnt(_)     -> acc
    | Repl(t,u)   -> params acc u
    | Delm(u)     -> params acc u
    | Hint(_,u)   -> params acc u

    | Coer(_,e,_) -> params acc e
    | Such(_,_,b) -> params acc (bseq_open b.binder)

    | SWit(_)     -> acc

    | Conv        -> acc
    | Succ(o)     -> params acc o
    | OWMu(_)     -> acc
    | OWNu(_)     -> acc
    | OSch(_)     -> acc
    | ESch(_)     -> acc

    | Vari _      -> acc
    | VPtr _      -> acc
    | TPtr _      -> acc
    | ITag _      -> assert false
  in
  (* The ordinals to be bound. *)
  let params = params Nil e in
  let assoc = mk_sassoc params in
  (* Binding function. *)
  let bind_all : type a. a ex loc -> a ebox =
    let mapper : type a. recall -> a ex loc -> a ebox = fun { default } e ->
      try
        let v = sassoc po e assoc in
        vari e.pos v
      with Not_found -> default e
    in
    fun e -> map ~mapper:{mapper} e
  in
  (* Building the actual binder. *)
  let rec bind : sassoc -> pbox -> pbox -> sbndr box = fun l e1 e2 ->
    match l with
    | Nil          -> box_apply2 (fun e1 e2 -> Cst(e1, e2)) e1 e2
    | Cns(s,_,v,l) -> box_apply (fun f -> Bnd(s,f))
                                (bind_var v (bind l e1 e2))
  in
  let fn e =
    match (unbox e).elt with
    | Prod m ->
       begin
         try  (lift (snd (A.find "1" m)), lift (snd (A.find "2" m)))
         with Not_found -> assert false
       end
    | _ -> assert false
  in
  let (p1, p2) = fn (bind_all e) in
  let b = bind assoc p1 p2 in
  (b, params)

let bind2_ordinals : Equiv.pool -> p ex loc -> p ex loc
    -> (o ex, sbndr) mbinder * ordi array = fun po e1 e2 ->
  let m = A.singleton "1" (None, e1) in
  let m = A.add "2" (None, e2) m in
  let e = Pos.none (Prod m) in
  let (b, os) = bind_ordinals e in
  (* Name for the corresponding variables. *)
  let names = mbinder_names b in
  (* The variables themselves. *)
  let xs = new_mvar (mk_free O) names in
  let p = msubst b (Array.map (mk_free O) xs) in
  let (b, ps) = bind_params po p in
  (unbox (bind_mvar xs b), os)

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
      (* NOTE: could compute variance of arguments ?, usefull for rose tree *)
      let rec fn : type a b. (a,b) fix_args -> (a,b) fbox = fun l ->
        match l with
        | Nil -> nil ()
        | Cns(a,l) -> cns (bind_all Any a) (fn l)
      in
      match (Norm.whnf e).elt with
      | HApp(s,f,e) -> happ None s (recall f) (bind_all Any e)
      | HDef(_,e)   -> recall e.expr_def
      | Func(t,a,b,l) -> func e.pos t l (bind_all (neg o) a) (recall b)
      | FixM(s, { elt = Conv},f,l) when o = Neg ->
         fixm e.pos s (new_ord ()) (bndr_name f)
              (fun x -> recall (bndr_subst f (mk_free s x))) (fn l)
      | FixN(s, { elt = Conv},f,l) when o = Pos ->
         fixn e.pos s (new_ord ()) (bndr_name f)
              (fun x -> recall (bndr_subst f (mk_free s x))) (fn l)
      | FixM(s,o1,f,l) when (Norm.whnf o1).elt <> Conv ->
         fixm e.pos s (search_ord o1) (bndr_name f)
              (fun x -> recall (bndr_subst f (mk_free s x))) (fn l)
      | FixN(s,o1,f,l) when (Norm.whnf o1).elt <> Conv ->
         fixn e.pos s (search_ord o1) (bndr_name f)
              (fun x -> recall (bndr_subst f (mk_free s x))) (fn l)
      | _        -> default e
    in
    map ~mapper:{mapper} e
  in
  let e = bind_all Pos e in
  let vars = Array.of_list !vars in
  let b = bind_mvar vars e in
  let os = Array.make (Array.length vars) (Pos.none Conv) in
  (unbox b, os)
