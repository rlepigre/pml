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

let no_bound_var : type a. a ex loc -> bool = fun e ->
  let open Iter in
  let iterator : type a. recall -> a ex loc -> unit = fun {default} e ->
    let e = Norm.whnf e in
    match e.elt with
    | Vari _   -> raise Exit
    | ITag _   -> raise Exit
    | _        -> default e
  in
  let iterator = { iterator; doclosed = false
                 ; dofixpnt = true
                 ; doepsiln = false }
  in
  try iter iterator e; true with Exit -> false

let occur_in : type a b. b ex loc -> a ex loc -> bool = fun f e ->
  let open Iter in
  let (fs,f) = sort f in
  let iterator : type a. recall -> a ex loc -> unit = fun {default} e ->
    Printf.printf "testing %a\n%!" Print.ex e;
    let (es, e) = sort e in
    match eq_sort fs es with
    | Eq -> if eq_expr e f then raise Exit else default e
    | NEq -> default e
  in
  let iterator = { iterator; doclosed = true
                 ; dofixpnt = true
                 ; doepsiln = false }
  in
  try iter iterator e; false with Exit -> true

let bind_ordinals : type a. a ex loc -> (o, a) mbndr * ordi array = fun e ->
  (* Compute the list of all the surface ordinal witnesses. *)
  let open Iter in
  let owits = ref ([] : o ex loc list) in
  let add e = if not (is_in e !owits) then owits := e :: !owits in
  let iterator : type a. recall -> a ex loc -> unit = fun {default} e ->
    match (Norm.whnf e).elt with
    | UWit(w)     ->
        begin
          let (s,_,_) = !(w.valu) in
          match s with
          | O -> add e
          | _ -> ()
        end
    | EWit(w)     ->
        begin
          let (s,_,_) = !(w.valu) in
          match s with
          | O -> add e
          | _ -> ()
        end
    | OWMu(_)     -> add e
    | OWNu(_)     -> add e
    | OSch(_)     -> add e
    | _           -> default e
  in
  let iterator = { iterator; doclosed = true
                 ; dofixpnt = true
                 ; doepsiln = false }
  in
  iter iterator e;
  (* The ordinals to be bound. *)
  let owits = !owits in
  let os = Array.of_list owits in
  let arity = Array.length os in
  (* Name for the corresponding variables. *)
  let xs = Array.init arity (Printf.sprintf "o%i") in
  (* The variables themselves. *)
  let xs = new_mvar (mk_free O) xs in
  (* Binding function. *)
  let bind_all : type a. a ex loc -> a ebox =
    let open Mapper in
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
  let rec fn = function
    | Nil          -> false
    | Cns(s1,e1,l) -> occur_in e1 e || fn l
  in
  fn l

let filter_slist : type a. a ex loc -> slist -> slist = fun e l ->
  let rec fn = function
    | Nil          -> Nil
    | Cns(s1,e1,l) -> if occur_in e e1 then l else Cns(s1,e1, fn l)
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
  let params = ref (Nil:slist) in
  let rec from_args : type a b. (a,b) fix_args -> unit = fun l ->
    match l with
    | Nil       -> ()
    | Cns(a, l) -> if no_bound_var a && not (in_slist a !params)
                   then
                     begin
                       let (s,a) = sort a in
                       match eq_sort s O with
                       | Eq  -> ()
                       | NEq -> params := Cns(s,a,filter_slist a !params)
                     end;
                   from_args  l
  in
  let open Iter in
  let iterator : type a. recall -> a ex loc -> unit = fun { default } e ->
    match (Norm.whnf e).elt with
    | FixM(s,o,f,l) -> let (_,t) = bndr_open f in
                       from_args l; default o; default t
    | FixN(s,o,f,l) -> let (_,t) = bndr_open f in
                       from_args l; default o; default t
    | _             -> default e
  in
  let iterator = { iterator; doclosed = true
                 ; dofixpnt = true
                 ; doepsiln = false }
  in
  iter iterator e;
  (* The ordinals to be bound. *)
  let params = !params in
  let assoc = mk_sassoc params in
  (* Binding function. *)
  let open Mapper in
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
