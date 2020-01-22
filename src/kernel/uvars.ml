(** Expression comparing and unification. *)

open Sorts
open Ast
open Pos
open Output

let log_uni = Log.register 'u' (Some "uni") "unification informations"
let log_uni = Log.(log_uni.p)

(* Unification variable equality test. *)
let uvar_eq : type a. a uvar -> a uvar -> bool =
  fun u v -> u.uvar_key == v.uvar_key

(** types used for the action in the iterator below *)
type uvar_fun = { f : 'a. 'a sort -> 'a uvar -> unit }
(** A small GADT for hash tbl below *)
type b = A : 'a ex -> b

exception Occurs

(** The iterator on unif variables appearing in an expression *)
let uvar_iter : type a. bool -> bool -> uvar_fun -> a ex loc -> unit =
  fun ignore_epsilon ignore_fixpoint f e ->
    let not_closed b = not (Bindlib.binder_closed (snd b)) in
    let adone = Ahash.create 67 in
    (** Function to test if epsilon should be tested *)
    let todo : type a . a ex loc -> bool =
      fun e ->
        not (ignore_epsilon) &&
          if Ahash.mem adone (A e.elt) then false
          else (
            Ahash.add adone (A e.elt) ();
            true)
    in
    let rec uvar_iter : type a. a ex loc -> unit = fun e ->
      (** iteration on conditions *)
      let uvar_iter_cond c =
        match c with
        | Equiv(t,_,u) -> uvar_iter t; uvar_iter u
        | NoBox(v)     -> uvar_iter v;
      in
      (** iteration on the list of unif variables used by epsilon *)
      let luvar_iter : type a b. (a, b) eps -> unit =
        fun w ->
          List.iter (fun (U(s,v)) ->
              match !(v.uvar_val) with
              | Set e   -> ()
              | Unset _ -> f.f s v
            ) !(w.vars)
      in
      let rec fuvar_iter : type a b. (a, b) fix_args -> unit =
        function
        | Nil -> ()
        | Cns(a,l) -> uvar_iter a; fuvar_iter l
      in
      (** iteration on binders *)
      let buvar_iter s b =
        if not_closed b then uvar_iter (bndr_term b)
      in
      let e = Norm.whnf e in
      match e.elt with
      | Vari(_)     -> ()
      | HFun(s,_,b) -> buvar_iter s b
      | HApp(_,a,b) -> uvar_iter a; uvar_iter b
      | HDef(_)     -> () (* NOTE no unification variable in definition. *)
      | Func(_,a,b,_) -> uvar_iter a; uvar_iter b
      | Prod(m)     -> A.iter (fun _ (_,a) -> uvar_iter a) m
      | DSum(m)     -> A.iter (fun _ (_,a) -> uvar_iter a) m
      | Univ(s,b)   -> buvar_iter s b
      | Exis(s,b)   -> buvar_iter s b
      | FixM(s,o,b,l) -> if not ignore_fixpoint then
                         (uvar_iter o; buvar_iter s b; fuvar_iter l)
      | FixN(s,o,b,l) -> if not ignore_fixpoint then
                         (uvar_iter o; buvar_iter s b; fuvar_iter l)
      | Memb(t,a)   -> uvar_iter t; uvar_iter a
      | Rest(a,c)   -> uvar_iter a; uvar_iter_cond c
      | Impl(c,a)   -> uvar_iter_cond c; uvar_iter a
      (* NOTE type annotation ignored. *)
      | LAbs(_,b,_) -> buvar_iter V b
      | Cons(_,v)   -> uvar_iter v
      | Reco(m)     -> A.iter (fun _ (_,a) -> uvar_iter a) m
      | Scis        -> ()
      | VDef(_)     -> () (* NOTE no unification variable in definition. *)
      | Valu(v)     -> uvar_iter v
      | Appl(t,u,_) -> uvar_iter t; uvar_iter u
      (* NOTE type annotation ignored. *)
      | MAbs(b)     -> buvar_iter S b
      | Name(s,t)   -> uvar_iter s; uvar_iter t
      | Proj(v,_)   -> uvar_iter v
      | Case(v,m)   -> let fn _ (_,b) = buvar_iter V b in
                       uvar_iter v; A.iter fn m
      | FixY(f)     -> buvar_iter T f
      | Prnt(_)     -> ()
      | Repl(t,u)   -> uvar_iter u (* Repl(_,u,_) = u *)
      | Delm(t)     -> uvar_iter t
      | Hint(_,t)   -> uvar_iter t

      | Conv        -> ()
      | Succ(o)     -> uvar_iter o
      (* NOTE type annotations ignored. *)
      | Coer(_,e,_) -> uvar_iter e
      | Such(_,_,r) -> uvar_iter (bseq_open r.binder)
      | Goal(_)     -> ()
      | VPtr(_)     -> ()
      | TPtr(_)     -> ()
      | VWit(w)     -> if todo e then luvar_iter w
      | SWit(w)     -> if todo e then luvar_iter w
      | UWit(w)     -> if todo e then luvar_iter w
      | EWit(w)     -> if todo e then luvar_iter w
      | OWMu(w)     -> if todo e then luvar_iter w
      | OWNu(w)     -> if todo e then luvar_iter w
      | OSch(i,o,w) -> begin
                         match o with
                         | None -> ()
                         | Some o -> uvar_iter o
                       end;
                       if todo e then luvar_iter w
      | ESch(s,i,w) -> if todo e then luvar_iter w
      | UVar(s,u)   -> f.f s u
      | ITag(_)     -> assert false
    in uvar_iter e

(** use the iterator to collect all variables in an expression *)
let uvars : type a. ?ignore_epsilon:bool -> ?ignore_fixpoint:bool
                 -> a ex loc -> s_elt list =
  fun ?(ignore_epsilon=false) ?(ignore_fixpoint=false) e ->
  let uvars = ref [] in
  let f s u =
    let p (U(_,v)) = v.uvar_key == u.uvar_key in
    if not (List.exists p !uvars) then uvars := (U(s,u)) :: !uvars
  in
  uvar_iter ignore_epsilon ignore_fixpoint {f} e; !uvars

(** use the iterator to collect all variables in a binder *)
let bndr_uvars : type a b. ?ignore_epsilon:bool -> ?ignore_fixpoint:bool
                      -> a sort -> (a, b) bndr -> s_elt list =
  fun ?(ignore_epsilon=false) ?(ignore_fixpoint=false) s b ->
    uvars ~ignore_epsilon ~ignore_fixpoint (bndr_term b)

let occur_chrono = Chrono.create "occur"

(** occur check *)
let uvar_occurs : type a b. a uvar -> b ex loc -> bool = fun u e ->
  let f _ v =
    if v.uvar_key == u.uvar_key then
      begin
        log_uni "Occur check on %d" u.uvar_key;
        raise Occurs
      end
  in
  if !(u.uvar_pur) && not (Pure.pure e) then true else
  try Chrono.add_time occur_chrono (uvar_iter false false {f}) e; false
  with Occurs -> true

(** Occur check in constraints *)
let uvar_occurs_rel : type a. a uvar -> rel -> bool = fun u c ->
  match c with
  | Equiv(t,_,s) -> uvar_occurs u t || uvar_occurs u s
  | NoBox(v)     -> uvar_occurs u v

(** count "visible" uvars *)
let nb_vis_uvars a =
  List.length (uvars ~ignore_epsilon:true ~ignore_fixpoint:true a)
