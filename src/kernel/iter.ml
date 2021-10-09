open Extra
open Ast
open Pos
open Sorts

(* a mapper may raise the exception Default *)
type recall = { recall : 'a. 'a ex loc -> unit
              ; default : 'a. 'a ex loc -> unit}
type iterator = { iterator : 'a. recall -> 'a ex loc -> unit
                ; doclosed : bool
                ; dofixpnt : bool
                ; doepsiln : bool
                }

let defiterator =
  let iterator {default} x = default x in
  { iterator
  ; doclosed = false
  ; dofixpnt = true
  ; doepsiln = true }

type b = A : 'a ex -> b

let iter : type a. iterator -> a ex loc -> unit
  = fun iterator e ->
    let itag_count = ref 0 in
    let itag : type a. a sort -> a ex =
      fun s -> let p = !itag_count in incr itag_count; ITag(s,p)
    in
    let adone = Ahash.create 67 in
    (** Function to test if epsilon should be tested *)
    let todo : type a . a ex loc -> bool =
      fun e ->
        iterator.doepsiln &&
          if Ahash.mem adone (A e.elt) then false
          else (
            Ahash.add adone (A e.elt) ();
            true)
    in
    let rec iter_cond c =
      match c with
      | Equiv(t,b,u) -> iter t; iter u
      | NoBox(v)     -> iter v

    and iter_args : type a b.(a, b) fix_args -> unit = fun l ->
      match l with
      | Nil      -> ()
      | Cns(e,l) -> iter e; iter_args l

    and biter : type a b. a sort -> (a, b) bndr -> unit = fun s b ->
      if iterator.doclosed || not (Bindlib.binder_closed (snd b)) then
        iter (bndr_subst b (itag s))
      else ()

    (** iteration on the list of unif variables used by epsilon *)
    and l_iter : type a b. (a, b) eps -> unit =
      fun w ->
      List.iter (fun (U(s,v)) -> iter (Pos.none (UVar(s,v)))) !(w.vars)

    and iter : type a. a ex loc -> unit = fun e ->
      let e = Norm.whnf e in
      let default : type a. a ex loc -> unit = fun e ->
        match e.elt with
        | HDef(_,_)     -> () (* Assumed closed *)
        | HApp(s,f,a)   -> iter f; iter a
        | HFun(a,b,f)   -> biter a f
        | UWit(w)       -> if todo e then l_iter w
        | EWit(w)       -> if todo e then l_iter w
        | UVar(_,_)     -> ()
        | ITag(_,_)     -> ()
        | Goal(_,_)     -> ()

        | Func(t,a,b,l) -> iter a; iter b
        | Prod(m)       -> A.iter (fun _ (_,a) -> iter a) m
        | DSum(m)       -> A.iter (fun _ (_,a) -> iter a) m
        | Univ(s,f)     -> biter s f
        | Exis(s,f)     -> biter s f
        | FixM(s,o,f,l) ->
           if iterator.dofixpnt then (iter o; biter s f; iter_args l)
        | FixN(s,o,f,l) ->
           if iterator.dofixpnt then (iter o; biter s f; iter_args l)
        | Memb(t,a)     -> iter t; iter a
        | Rest(a,c)     -> iter a; iter_cond c
        | Impl(c,a)     -> iter_cond c; iter a

        | VWit(w)       -> if todo e then l_iter w
        | LAbs(a,f,l)   -> biter V f
        | Cons(c,v)     -> iter v
        | Reco(m)       -> A.iter (fun _ (_,v) -> iter v) m
        | Scis          -> ()
        | VDef(_)       -> () (* Assumed closed *)
        | CPsi          -> ()
        | Clck(v)       -> iter v

        | Coer(t,e,a)   -> iter e
        | Such(t,d,r)   -> iter (bseq_open r.binder)

        | Valu(v)       -> iter v
        | Appl(t,u,_)   -> iter t; iter u
        | MAbs(f)       -> biter S f
        | Name(s,t)     -> iter s; iter t
        | Proj(v,l)     -> iter v
        | Case(v,m)     -> let fn _ (_,f) = biter V f  in
                           iter v; A.iter fn m
        | FixY(f)       -> biter T f
        | Prnt(s)       -> ()
        | Repl(t,u)     -> iter u
        | Delm(u)       -> iter u
        | Hint(h,u)     -> iter u

        | SWit(w)       -> if todo e then l_iter w

        | Conv          -> ()
        | Succ(o)       -> iter o
        | OWMu(w)       -> if todo e then l_iter w
        | OWNu(w)       -> if todo e then l_iter w
        | OSch(i,o,w)   -> begin
                             match o with
                             | None -> ()
                             | Some o -> iter o
                           end;
                           if todo e then l_iter w
        | ESch(_,_,w)   -> if todo e then l_iter w
        | Vari(_,x)     -> ()

        | VPtr _        -> ()
        | TPtr _        -> ()
        in
        iterator.iterator { recall = iter; default } e
      in iter e
