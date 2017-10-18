(** Expression comparing and unification. *)

open Bindlib
open Sorts
open Ast
open Pos
open Output

let log_uni = Log.register 'u' (Some "uni") "unification informations"
let log_uni = Log.(log_uni.p)

(* Unification variable equality test. *)
let uvar_eq : type a. a uvar -> a uvar -> bool =
  fun u v -> u.uvar_key == v.uvar_key

let exists_set l =
  List.exists (fun (U(_,v)) ->
      match !(v.uvar_val) with Set _ -> true | _ -> false) l

type uvar_fun = { f : 'a. 'a sort -> 'a uvar -> unit }

type b = A : 'a ex -> b

let uvar_iter : type a. bool -> bool -> uvar_fun -> a ex loc -> unit =
  fun ignore_epsilon ignore_fixpoint f e ->
  let not_closed b = not (Bindlib.binder_closed (snd b)) in
  let adone = Ahash.create 67 in
  let todo : type a . a ex loc -> bool =
  fun e ->
      not (ignore_epsilon) &&
        if Ahash.mem adone (A e.elt) then false
        else (
          Ahash.add adone (A e.elt) ();
          true)
  in
  let rec uvar_iter : type a. a ex loc -> unit = fun e ->
    let uvar_iter_cond c =
      match c with
      | Equiv(t,_,u) -> uvar_iter t; uvar_iter u
      | NoBox(v)     -> uvar_iter v;
      | Posit(o)     -> uvar_iter o
    in
    let luvar_iter : type a.a eps -> unit =
      fun w -> w.refr ();
               List.iter (fun (U(s,v)) -> f.f s v) !(w.vars)
    in
    let buvar_iter b = if not_closed b then uvar_iter (bndr_subst b Dumm) in
    let e = Norm.whnf e in
    match e.elt with
    | Vari(_)     -> ()
    | HFun(_,_,b) -> buvar_iter b
    | HApp(_,a,b) -> uvar_iter a; uvar_iter b
    | HDef(_)     -> () (* NOTE no unification variable in definition. *)
    | Func(a,b)   -> uvar_iter a; uvar_iter b
    | Prod(m)     -> A.iter (fun _ (_,a) -> uvar_iter a) m
    | DSum(m)     -> A.iter (fun _ (_,a) -> uvar_iter a) m
    | Univ(_,b)   -> buvar_iter b
    | Exis(_,b)   -> buvar_iter b
    | FixM(o,b)   -> if not ignore_fixpoint then (uvar_iter o; buvar_iter b)
    | FixN(o,b)   -> if not ignore_fixpoint then (uvar_iter o; buvar_iter b)
    | Memb(t,a)   -> uvar_iter t; uvar_iter a
    | Rest(a,c)   -> uvar_iter a; uvar_iter_cond c
    | Impl(c,a)   -> uvar_iter_cond c; uvar_iter a
    (* NOTE type annotation ignored. *)
    | LAbs(_,b)   -> buvar_iter b
    | Cons(_,v)   -> uvar_iter v
    | Reco(m)     -> A.iter (fun _ (_,a) -> uvar_iter a) m
    | Scis        -> ()
    | VDef(_)     -> () (* NOTE no unification variable in definition. *)
    | Valu(v)     -> uvar_iter v
    | Appl(t,u)   -> uvar_iter t; uvar_iter u
    (* NOTE type annotation ignored. *)
    | MAbs(b)     -> buvar_iter b
    | Name(s,t)   -> uvar_iter s; uvar_iter t
    | Proj(v,_)   -> uvar_iter v
    | Case(v,m)   -> let fn _ (_,b) = buvar_iter b in
                     uvar_iter v; A.iter fn m
    | FixY(f,v)   -> buvar_iter f; uvar_iter v
    | Prnt(_)     -> ()
    | Epsi        -> ()
    | Push(v,s)   -> uvar_iter v; uvar_iter s
    | Fram(t,s)   -> uvar_iter t; uvar_iter s
    | Conv        -> ()
    | Succ(o)     -> uvar_iter o
    (* NOTE type annotations ignored. *)
    | Coer(_,e,_) -> uvar_iter e
    | Such(_,_,r) -> uvar_iter (bseq_dummy r.binder)
    | ITag(_)     -> ()
    | Dumm        -> ()
    | Goal(_)     -> ()
    | VPtr(_)     -> ()
    | TPtr(_)     -> ()
    | VWit(w)     -> if todo e then luvar_iter w
    | SWit(w)     -> if todo e then luvar_iter w
    | UWit(w)     -> if todo e then luvar_iter w
    | EWit(w)     -> if todo e then luvar_iter w
    | OWMu(w)     -> if todo e then luvar_iter w
    | OWNu(w)     -> if todo e then luvar_iter w
    | OSch(i,w)   -> if todo e then luvar_iter w
    | UVar(s,u)   -> f.f s u
  in uvar_iter e

let uvars : type a. ?ignore_epsilon:bool -> ?ignore_fixpoint:bool
                 -> a ex loc -> s_elt list =
  fun ?(ignore_epsilon=false) ?(ignore_fixpoint=false) e ->
  let uvars = ref [] in
  let f s u =
    let p (U(_,v)) = v.uvar_key == u.uvar_key in
    if not (List.exists p !uvars) then uvars := (U(s,u)) :: !uvars
  in
  uvar_iter ignore_epsilon ignore_fixpoint {f} e; !uvars

let bndr_uvars : type a b. ?ignore_epsilon:bool -> ?ignore_fixpoint:bool
                      -> (a, b) bndr -> s_elt list =
  fun ?(ignore_epsilon=false) ?(ignore_fixpoint=false) b ->
  uvars ~ignore_epsilon ~ignore_fixpoint (bndr_subst b Dumm)

let occur_chrono = Chrono.create "occur"

let uvar_occurs : type a b. a uvar -> b ex loc -> bool = fun u e ->
  let f _ v =
    if v.uvar_key == u.uvar_key then
      begin
        log_uni "Occur check on %d" u.uvar_key;
        raise Exit
      end
  in
  try Chrono.add_time occur_chrono (uvar_iter false false {f}) e; false
  with Exit -> true

let nb_vis_uvars a =
  List.length (uvars ~ignore_epsilon:true ~ignore_fixpoint:true a)

let uvar_occurs_rel : type a. a uvar -> rel -> bool = fun u c ->
  match c with
  | Equiv(t,_,s) -> uvar_occurs u t || uvar_occurs u s
  | NoBox(v)     -> uvar_occurs u v;
  | Posit(o)     -> uvar_occurs u o