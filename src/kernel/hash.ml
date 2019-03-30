(** Expression hashing. *)

module E = Effect
open Bindlib
open Sorts
open Pos
open Ast

type hash =
  { hash_expr     : 'a. 'a ex loc -> int
  ; hash_bndr     : 'a 'b. 'a sort -> ('a,'b) bndr -> int
  ; hash_ombinder : 'a. (o ex, 'a ex loc) mbinder -> int
  ; hash_vwit     : vwit -> int
  ; hash_qwit     : 'a. 'a qwit -> int
  ; hash_owit     : owit -> int
  ; hash_swit     : swit -> int
  ; hash_cwit     : schema -> int
  }

(* hash functions *)
let {hash_expr; hash_bndr; hash_ombinder; hash_vwit
    ; hash_qwit; hash_owit; hash_swit; hash_cwit} =
  let c = ref (-1) in
  let new_itag : type a. a sort -> a ex = fun s -> incr c; ITag(s,!c) in
  let hash : type a. a -> int = Hashtbl.hash in
  let mix x y = ((y lsl 17) - x) lxor ((x lsr 7) - y) in
  let mix3 x y z = mix x (mix y z) in
  let khash1 k x = mix (hash k) x in
  let khash2 k x y = mix (hash k) (mix x y) in
  let khash3 k x y z = mix (mix (hash k) x) (mix y z) in
  let khash4 k x y z t = mix (mix (hash k) x) (mix y (mix z t)) in
  let rec hash_expr : type a. a ex loc -> int =
    fun e ->
    let hash_cond = function
      | Equiv(t,b,u) -> khash3 `Equiv (hash_expr t) (hash b) (hash_expr u)
      | NoBox(v)     -> hash (`NoBox(hash_expr v))
    in
    let rec hash_args : type a b. (a,b) fix_args -> int = function
      | Nil      -> hash `Nil
      | Cns(a,l) -> khash2 `Cns (hash_expr a) (hash_args l)
    in
    let e = Norm.whnf e in
    match e.elt with
    | HDef(_,d)   -> d.expr_hash
    | VDef(d)     -> d.value_hash
    | Valu(v)     -> hash_expr v
    | Coer(_,e,_) -> hash_expr e
    | Such(_,_,r) -> hash_expr (bseq_dummy r.binder)
    | PSet(_,_,e) -> hash_expr e
    | Vari(_,x)   -> khash1 `Vari (Bindlib.hash_var x)
    | HFun(s,_,b) -> khash1 `HFun (hash_bndr s b)
    | HApp(s,f,a) -> khash3 `HApp (hash_sort s) (hash_expr f) (hash_expr a)
    | Func(t,a,b) -> khash3 `Func (E.hash t) (hash_expr a) (hash_expr b)
    | DSum(m)     -> khash1 `DSum (A.hash (fun (_,e) -> hash_expr e) m)
    | Prod(m)     -> khash1 `Prod (A.hash (fun (_,e) -> hash_expr e) m)
    | Univ(s,b)   -> khash2 `Univ (hash_sort s) (hash_bndr s b)
    | Exis(s,b)   -> khash2 `Exit (hash_sort s) (hash_bndr s b)
    | FixM(s,o,b,l)
                  -> khash4 `FixM (hash_sort s) (hash_expr o)
                            (hash_bndr s b) (hash_args l)
    | FixN(s,o,b,l)
                  -> khash4 `FixN (hash_sort s) (hash_expr o)
                            (hash_bndr s b) (hash_args l)
    | Memb(t,a)   -> khash2 `Memb (hash_expr t) (hash_expr a)
    | Rest(a,c)   -> khash2 `Rest (hash_expr a) (hash_cond c)
    | Impl(c,a)   -> khash2 `Impl (hash_expr a) (hash_cond c)
    (* NOTE type annotation ignored. *)
    | LAbs(_,b,_) -> khash1 `LAbs (hash_bndr V b)
    | Cons(c,v)   -> khash2 `Cons (hash c.elt) (hash_expr v)
    | Reco(m)     -> khash1 `Reco (A.hash (fun (_,e) -> hash_expr e) m)
    | Scis        -> hash `Scis
    | Appl(t,u)   -> khash2 `Appl (hash_expr t) (hash_expr u)
    (* NOTE type annotation ignored. *)
    | MAbs(b)     -> khash1 `MAbs (hash_bndr S b)
    | Name(s,t)   -> khash2 `Name (hash_expr s) (hash_expr t)
    | Proj(v,l)   -> khash2 `Proj (hash l.elt) (hash_expr v)
    | Case(v,m)   -> khash2 `Case (hash_expr v)
                            (A.hash (fun (_,e) -> (hash_bndr V e)) m)
    | FixY(_,f)   -> hash (`FixY (hash_bndr T f))
    | Prnt(s1)    -> khash1 `Prnt (hash s1)
    | Repl(_,u)   -> hash_expr u
    | Delm(u)     -> hash_expr u
    | Conv        -> hash `Conv
    | Succ(o)     -> khash1 `Succ (hash_expr o)
    (* NOTE type annotations ignored. *)
    | ITag(_,i)   -> hash (`ITag(i))
    (* NOTE should not be compare dummy expressions. *)
    | Dumm(s)     -> khash1 `Dumm (hash_sort s)
    | VWit(w)     -> w.refr (); khash1 `VWit !(w.hash)
    | SWit(w)     -> w.refr (); khash1 `SWit !(w.hash)
    | UWit(w)     -> w.refr (); khash1 `UWit !(w.hash)
    | EWit(w)     -> w.refr (); khash1 `EWit !(w.hash)
    | OWMu(w)     -> w.refr (); khash1 `OWMu !(w.hash)
    | OWNu(w)     -> w.refr (); khash1 `OWNu !(w.hash)
    | OSch(i,o,w) -> w.refr (); khash3 `OSch i (hash_opt_expr o) !(w.hash)
    | ESch(_,i,w) -> w.refr (); khash2 `ESch i !(w.hash)
    | UVar(i,u)   -> khash1 `UVar u.uvar_key
    (* two next cases are automatically stronger with oracle *)
    | VPtr v      -> khash1 `VPtr (hash v)
    | TPtr t      -> khash1 `TPtr (hash t)
    | Goal(s,str) -> khash2 `Goal (hash_sort s) (hash str)

  and hash_bndr : type a b. a sort -> (a,b) bndr -> int =
    fun s b ->
      let t = new_itag s in
      hash_expr (bndr_subst b t)

  and hash_ombinder : type a. (o ex, a ex loc) mbinder -> int =
    fun omb ->
      let ar = mbinder_arity omb in
      let ta = Array.init ar (fun _ -> new_itag O) in
      hash_expr (msubst omb ta)

  and hash_opt_expr = function
    | None -> hash `None
    | Some e -> khash1 `Some (hash_expr e)

  and hash_vwit : vwit -> int =
    fun (f,a,b) -> mix3 (hash_bndr V f) (hash_expr a) (hash_expr b)

  and hash_qwit : type a. a qwit -> int =
    fun (s,t,b) -> mix3 (hash_sort s) (hash_expr t) (hash_bndr s b)

  and hash_owit : owit -> int =
    fun (s,t,b) -> mix3 (hash_expr s) (hash_expr t) (hash_bndr O b)

  and hash_swit : swit -> int =
    fun (b,t) -> mix (hash_bndr S b) (hash_expr t)

  and hash_cwit : schema -> int =
    function
      | FixSch s -> khash1 `FixSch (hash s.fsch_index)
      | SubSch s -> khash1 `SubSch (hash s.ssch_index)
  in

  let hash_chrono = Chrono.create "hash" in

  let hash_expr : type a. a ex loc -> int =
    fun e ->
      c := -1; (* Reset. *)
      Chrono.add_time hash_chrono hash_expr e
  in

  let hash_bndr : type a b. a sort -> (a,b) bndr -> int =
    fun s b ->
      c := -1; (* Reset. *)
      Chrono.add_time hash_chrono (hash_bndr s) b
  in

  let hash_ombinder : type a. (o ex, a ex loc) mbinder -> int =
    fun omb ->
      c := -1; (* Reset. *)
      Chrono.add_time hash_chrono hash_ombinder omb
  in

  let hash_vwit = fun w ->
      c := -1; (* Reset. *)
      Chrono.add_time hash_chrono hash_vwit w
  in

  let hash_qwit = fun w ->
      c := -1; (* Reset. *)
      Chrono.add_time hash_chrono hash_qwit w
  in

  let hash_owit = fun w ->
      c := -1; (* Reset. *)
      Chrono.add_time hash_chrono hash_owit w
  in
  { hash_expr; hash_bndr; hash_ombinder; hash_vwit
  ; hash_qwit; hash_owit; hash_swit; hash_cwit }
