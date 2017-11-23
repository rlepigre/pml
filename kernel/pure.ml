(** Purity test *)

open Bindlib
open Sorts
open Ast
open Pos
open Output
open Totality

type b = A : 'a ex -> b

let pure : type a. a ex loc -> bool =
  fun e ->
  let adone = Ahash.create 67 in
  let todo : type a . a ex loc -> bool =
    fun e ->
      if Ahash.mem adone (A e.elt) then false
      else (
        Ahash.add adone (A e.elt) ();
        true)
  in
  let rec iter : type a. a ex loc -> unit = fun e ->
    let iter_cond c =
      match c with
      | Equiv(t,_,u) -> iter t; iter u
      | NoBox(v)     -> iter v;
      | Posit(o)     -> iter o
    in
    let liter : type a b. (a, b) eps -> unit =
      fun w -> w.refr ();
               if not !(w.pure) then raise Exit;
               List.iter (fun (U(s,v)) -> iter (Pos.none (UVar(s,v)))) !(w.vars)
    in
    let biter s b = iter (bndr_subst b (Dumm s)) in
    let e = Norm.whnf e in
    match e.elt with
    | Vari(_)     -> ()
    | HFun(s,_,b) -> biter s b
    | HApp(_,a,b) -> iter a; iter b
    | HDef(_)     -> () (* NOTE no unification variable in definition. *)
    | Func(t,a,b) -> if not Totality.(sub Tot t) then raise Exit;
                     iter a; iter b
    | Prod(m)     -> A.iter (fun _ (_,a) -> iter a) m
    | DSum(m)     -> A.iter (fun _ (_,a) -> iter a) m
    | Univ(s,b)   -> biter s b
    | Exis(s,b)   -> biter s b
    | FixM(o,b)   -> iter o; biter P b
    | FixN(o,b)   -> iter o; biter P b
    | Memb(t,a)   -> iter t; iter a
    | Rest(a,c)   -> iter a; iter_cond c
    | Impl(c,a)   -> iter_cond c; iter a
    (* NOTE type annotation ignored. *)
    | LAbs(_,b)   -> biter V b
    | Cons(_,v)   -> iter v
    | Reco(m)     -> A.iter (fun _ (_,a) -> iter a) m
    | Scis        -> ()
    | VDef(_)     -> () (* NOTE no unification variable in definition. *)
    | Valu(v)     -> iter v
    | Appl(t,u)   -> iter t; iter u
    (* NOTE type annotation ignored. *)
    | MAbs(b)     -> biter S b
    | Name(s,t)   -> iter s; iter t
    | Proj(v,_)   -> iter v
    | Case(v,m)   -> let fn _ (_,b) = biter V b in
                     iter v; A.iter fn m
    | FixY(f)     -> biter T f
    | Prnt(_)     -> ()
    | Repl(t,u,a) -> iter t; iter u; iter a
    | Delm(u)     -> iter u
    | Conv        -> ()
    | Succ(o)     -> iter o
    (* NOTE type annotations ignored. *)
    | Coer(_,e,_) -> iter e
    | Such(_,_,r) -> iter (bseq_dummy r.binder)
    | ITag(_)     -> ()
    | Dumm(_)     -> ()
    | Goal(_)     -> ()
    | VPtr(_)     -> ()
    | TPtr(_)     -> ()
    | VWit(w)     -> if todo e then liter w
    | SWit(w)     -> if todo e then liter w
    | UWit(w)     -> if todo e then liter w
    | EWit(w)     -> if todo e then liter w
    | OWMu(w)     -> if todo e then liter w
    | OWNu(w)     -> if todo e then liter w
    | OSch(i,o,w) -> begin
                       match o with
                       | None -> ()
                       | Some o -> iter o
                     end;
                     if todo e then liter w
    | UVar(s,u)   -> UTimed.(u.uvar_pur := true)
  in
  try iter e; true with Exit -> false

let pure_schema = function
  | FixSch s ->
     let (b, mb) = s.fsch_judge in
     pure (bndr_subst b (Dumm T)) &&
       pure (msubst mb (Array.make (mbinder_arity mb) (Dumm O)))
  | SubSch s ->
     let mb = s.ssch_judge in
     let (a,b) = msubst mb (Array.make (mbinder_arity mb) (Dumm O)) in
     pure a && pure b
