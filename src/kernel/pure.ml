(** Purity test *)

open Bindlib
open Sorts
open Ast
open Pos

(** type for the hashtbl below *)
type b = A : 'a ex -> b

(** Iterator testing purity of an expression, that is the fact that
    it uses only total (a.k.a. intuitionnistic) arrows (=>) *)
let pure : type a. a ex loc -> bool =
  fun e ->
  let adone = Ahash.create 67 in
  (** test if epsilon are already done *)
  let todo : type a . a ex loc -> bool =
    fun e ->
      if Ahash.mem adone (A e.elt) then false
      else (
        Ahash.add adone (A e.elt) ();
        true)
  in
  let rec iter : type a. a ex loc -> unit = fun e ->
    (** iterator for epsilon: purity is keps as a lazy bool,
        but we must set the lazy constraint on variable that appears
        in the epsilons *)
    let liter : type a b. (a, b) eps -> unit =
      fun w -> if not (Lazy.force !(w.pure)) then raise Exit;
        List.iter (fun (U(s,v)) -> iter (Pos.none (UVar(s,v)))) !(w.vars)
    in
    (** iteration on binders *)
    let biter s b = iter (bndr_term b) in
    let rec fiter : type a b. (a, b) fix_args -> unit
      = function
      | Nil -> ()
      | Cns(a,l) -> iter a; fiter l
    in
    let e = Norm.whnf e in
    match e.elt with
    | Vari(_)     -> ()
    | HFun(s,_,b) -> biter s b
    | HApp(_,a,b) -> iter a; iter b
    | HDef(_,d)   -> iter d.expr_def
    | Func(t,a,b,_)
                  -> if not Effect.(absent CallCC t) then raise Exit;
                     iter a; iter b
    | Prod(m)     -> A.iter (fun _ (_,a) -> iter a) m
    | DSum(m)     -> A.iter (fun _ (_,a) -> iter a) m
    | Univ(s,b)   -> biter s b
    | Exis(s,b)   -> biter s b
    | FixM(s,o,b,l)
                  -> iter o; biter s b; fiter l
    | FixN(s,o,b,l)
                  -> iter o; biter s b; fiter l
    | Memb(t,a)   -> iter a
    | Rest(a,c)   -> iter a
    | Impl(c,a)   -> iter a
    (* NOTE type annotation ignored. *)
    | LAbs(_,b,_) -> biter V b
    | Cons(_,v)   -> iter v
    | Reco(m)     -> A.iter (fun _ (_,a) -> iter a) m
    | Scis        -> ()
    | VDef(d)     -> () (* no type in value def *)
    | Valu(v)     -> iter v
    | Appl(t,u,_) -> iter t; iter u
    | Hint(_,t)   -> iter t

    (* NOTE type annotation ignored. *)
    | MAbs(b)     -> biter S b
    | Name(s,t)   -> iter s; iter t
    | Proj(v,_)   -> iter v
    | Case(v,m)   -> let fn _ (_,b) = biter V b in
                     iter v; A.iter fn m
    | FixY(f)     -> biter T f
    | Prnt(_)     -> ()
    | Repl(t,u)   -> iter u (* Repl(_,_) = u *)
    | Delm(u)     -> iter u
    | Conv        -> ()
    | Succ(o)     -> iter o
    (* NOTE type annotations ignored. *)
    | Coer(_,e,_) -> iter e
    | Such(_,_,r) -> iter (bseq_open r.binder)
    | ITag(_)     -> ()
    | Goal(_)     -> ()
    | VPtr(_)     -> ()
    | TPtr(_)     -> ()
    | VWit(w)     -> ()
    | SWit(w)     -> raise Exit
    | UWit(w)     -> if todo e then liter w
    | EWit(w)     -> if todo e then liter w
    | OWMu(w)     -> ()
    | OWNu(w)     -> ()
    | OSch(i,o,w) -> ()
    | ESch(s,i,w) -> if todo e then liter w
    | UVar(s,u)   -> UTimed.(u.uvar_pur := true)
  in
  try iter e; true with Exit -> false

(** purity test for schemas *)
let pure_schema = function
  | FixSch s ->
     let (b, mb) = s.fsch_judge in
     pure (bndr_term b) &&
       pure (snd (unmbind mb))
  | SubSch s ->
     let mb = s.ssch_judge in
     let (_,f) = unmbind mb in
     let rec fn = function
       | Cst(a,b) -> pure a && pure b
       | Bnd(s,f) -> fn (snd (unbind f))
     in
     fn f
