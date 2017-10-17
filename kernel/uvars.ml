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
    | VPtr(_)     -> assert false
    | TPtr(_)     -> assert false
    | VWit(_,w)   -> let (f,a,b) = w in
                     if todo e then (buvar_iter f; uvar_iter a; uvar_iter b)
    | SWit(_,w)   -> let (b,a) = w in
                     if todo e then (buvar_iter b; uvar_iter a)
    | UWit(_,_,w) -> let (t,b) = w in
                     if todo e then (uvar_iter t; buvar_iter b)
    | EWit(_,_,w) -> let (t,b) = w in
                     if todo e then (uvar_iter t; buvar_iter b)
    | OWMu(_,w)   -> let (o,t,b) = w in
                     if todo e then (uvar_iter o; uvar_iter t; buvar_iter b)
    | OWNu(_,w)   -> let (o,t,b) = w in
                     if todo e then (uvar_iter o; uvar_iter t; buvar_iter b)
    | OSch(_,w)   ->
       let (o,i,s) = w in
       if todo e then
         begin
           match s with
           | FixSch s ->
              let (t,b) = s.fsch_judge in
              let (_,t) = Bindlib.unbind (mk_free V) (snd t) in
              let (_,k) = Bindlib.unmbind (mk_free O) b in
              Extra.Option.iter uvar_iter o; uvar_iter t; uvar_iter k
           | SubSch s ->
              let b = s.ssch_judge in
              let (_,(k1,k2)) = Bindlib.unmbind (mk_free O) b in
              Extra.Option.iter uvar_iter o; uvar_iter k1; uvar_iter k2
         end
    | UVar(s,u)   -> f.f s u
  in uvar_iter e

type s_elt = U : 'a sort * 'a uvar -> s_elt

let uvars : type a. ?ignore_epsilon:bool -> ?ignore_fixpoint:bool
                 -> a ex loc -> s_elt list =
  fun ?(ignore_epsilon=false) ?(ignore_fixpoint=false) e ->
  let uvars = ref [] in
  let f s u =
    let p (U(_,v)) = v.uvar_key == u.uvar_key in
    if not (List.exists p !uvars) then uvars := (U(s,u)) :: !uvars
  in
  uvar_iter ignore_epsilon ignore_fixpoint {f} e; !uvars

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
