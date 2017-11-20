(** Equivalence decision procedure. During decision of equivalence, terms are
    stored in a graph (shared among all knonwn terms). Maximal sharing is
    attained by never inserting nodes that are already in the graph. Given
    such a graph (or pool), one will be able to read back the representative
    of a term by following the edges. *)

open Extra
open Bindlib
open Ptr
open Sorts
open Pos
open Ast
open Output
open Uvars
open Compare
open Epsilon

let equiv_chrono = Chrono.create "equiv"
let pareq_chrono = Chrono.create "pareq"
let inser_chrono = Chrono.create "inser"

(* Log function registration. *)
let log_edp1 =
  Log.register 'e' (Some "equ") "equivalence decision procedure"
let log_edp2 =
  Log.register 'f' (Some "equ") "details of equivalence decision"
let log  = Log.(log_edp1.p)
let log2 = Log.(log_edp2.p)

(** Exception raise when the pool contains a contradiction. *)
exception Contradiction
let bottom () = raise Contradiction

type ('a, 'b) funptr = (v ex, (t ex, ('a, 'b) bndr) mbinder) mbinder

let hash_funptr : type a b.a sort -> (a, b) funptr -> int =
  fun s b ->
    let c = ref 0 in
    let new_itag : type a. a sort -> a ex = fun s -> decr c; ITag(s,!c) in
    let a = mbinder_arity b in
    let vs = Array.init a (fun _ -> new_itag V) in
    let b = msubst b vs in
    let a = mbinder_arity b in
    let ts = Array.init a (fun _ -> new_itag T) in
    let b = msubst b ts in
    hash_bndr s b

let eq_funptr : type a b.a sort -> (a, b) funptr -> (a, b) funptr -> bool =
  fun s b1 b2 ->
    let c = ref 0 in
    let new_itag : type a. a sort -> a ex = fun s -> decr c; ITag(s,!c) in
    let a1 = mbinder_arity b1 in
    let a2 = mbinder_arity b2 in
    a1 = a2 && (
      let vs = Array.init a1 (fun _ -> new_itag V) in
      let b1 = msubst b1 vs in
      let b2 = msubst b2 vs in
      let a1 = mbinder_arity b1 in
      let a2 = mbinder_arity b2 in
      a1 = a2 && (
        let ts = Array.init a1 (fun _ -> new_itag T) in
        let b1 = msubst b1 ts in
        let b2 = msubst b2 ts in
        eq_bndr s b1 b2))

type anyfunptr = T : 'a sort * 'b sort * ('a, 'b) funptr -> anyfunptr
module Fun =
  struct
    type t = anyfunptr

    let equal (T (sa1,sr1,f1)) (T (sa2,sr2,f2)) =
      match eq_sort sa1 sa2 with
      | Eq.Eq ->
         begin
           match eq_sort sr1 sr2 with
           | Eq.Eq -> eq_funptr sa1 f1 f2
           | _ -> false
         end
      | _ -> false

    let hash (T (sa,sr,f)) =
      Hashtbl.hash (hash_sort sa, hash_sort sr, hash_funptr sa f)
  end
module FunHash = Hashtbl.Make(Fun)

type ('a,'b) bndr_closure = ('a, 'b) funptr * VPtr.t array * Ptr.t array

type 'a clsptr = (v ex, (t ex, 'a ex loc) mbinder) mbinder

let hash_clsptr : type a. a clsptr -> int =
  fun b ->
    let c = ref 0 in
    let new_itag : type a. a sort -> a ex = fun s -> decr c; ITag(s,!c) in
    let a = mbinder_arity b in
    let vs = Array.init a (fun _ -> new_itag V) in
    let b = msubst b vs in
    let a = mbinder_arity b in
    let vs = Array.init a (fun _ -> new_itag T) in
    let b = msubst b vs in
    hash_expr b

let eq_clsptr : type a. a clsptr -> a clsptr -> bool =
  fun b1 b2 ->
    let c = ref 0 in
    let new_itag : type a. a sort -> a ex = fun s -> decr c; ITag(s,!c) in
    let a1 = mbinder_arity b1 in
    a1 = (mbinder_arity b2) && (
      let vs = Array.init a1 (fun _ -> new_itag V) in
      let b1 = msubst b1 vs in
      let b2 = msubst b2 vs in
      let a1 = mbinder_arity b1 in
      a1 = (mbinder_arity b2) && (
        let vs = Array.init a1 (fun _ -> new_itag T) in
        let b1 = msubst b1 vs in
        let b2 = msubst b2 vs in
        eq_expr b1 b2))

type anyclsptr = C : 'a sort * 'a clsptr -> anyclsptr
module Cls =
  struct
    type t = anyclsptr

    let equal (C (sa1,f1)) (C (sa2,f2)) =
      match eq_sort sa1 sa2 with
      | Eq.Eq -> eq_clsptr f1 f2
      | _ -> false

    let hash (C (sa,f)) =
      Hashtbl.hash (hash_sort sa, hash_clsptr f)
  end
module ClsHash = Hashtbl.Make(Cls)

type 'a closure = 'a clsptr * VPtr.t array * Ptr.t array

let subst_closure (funptr,vs,ts) =
  let vs = Array.map (fun v -> VPtr v) vs in
  let ts = Array.map (fun t -> TPtr t) ts in
  msubst (msubst funptr vs) ts

(** Wrapper for higher-order application. *)
type _ ho_appl =
  | HO : 'a sort * ('a -> 'b) closure * 'a closure -> 'b ho_appl

(** Type of a value node. *)
type v_node =
  | VN_LAbs of (v, t) bndr_closure
  | VN_Cons of A.key loc * VPtr.t
  | VN_Reco of VPtr.t A.t
  | VN_Scis
  | VN_VWit of (vwit, string) eps
  | VN_UWit of (v qwit, string) eps
  | VN_EWit of (v qwit, string) eps
  | VN_HApp of v ho_appl
  | VN_UVar of v uvar
  | VN_ITag of int
  | VN_Goal of v ex loc

(** Type of a term node. *)
type t_node =
  | TN_Valu of VPtr.t
  | TN_Appl of Ptr.t * Ptr.t
  | TN_MAbs of (s,t) bndr_closure
  | TN_Name of s ex loc * Ptr.t
  | TN_Proj of VPtr.t * A.key loc
  | TN_Case of VPtr.t * (v,t) bndr_closure A.t
  | TN_FixY of (t,v) bndr_closure
  | TN_Prnt of string
  | TN_UWit of (t qwit, string) eps
  | TN_EWit of (t qwit, string) eps
  | TN_HApp of t ho_appl
  | TN_UVar of t uvar
  | TN_ITag of int
  | TN_Goal of t ex loc

type _ ty += T_Node : t_node ty
           | V_Node : v_node ty

(** Printing closure. *)
let pcl : type a. out_channel -> a closure -> unit =
  fun ch (funptr,vs,ts) ->
    let prnt = Printf.fprintf in
    let pex = Print.ex in
    let (vvars,b) = unmbind (mk_free V) funptr in
    let (tvars,t) = unmbind (mk_free T) b in
    let vvars = if vs = [||] then [||] else vvars in
    let tvars = if ts = [||] then [||] else tvars in
    let fn ch =
      Array.iteri (fun i v ->
          let t = vs.(i) in
          let sep = if i = 0 then "" else ", " in
          prnt ch "%s%s<-%a" sep (name_of v) VPtr.print t) vvars
    in
    let gn ch =
      Array.iteri (fun i v ->
          let t = ts.(i) in
          let sep = if i = 0 then "" else ", " in
          prnt ch "%s%s<-%a" sep (name_of v) Ptr.print t) tvars
    in
    prnt ch "%a[%t][%t]" pex t fn gn

(** Printing function for value nodes. *)
let pbcl : type a b. a sort -> out_channel -> (a, b) bndr_closure -> unit =
  fun s ch (funptr,vs,ts) ->
    let prnt = Printf.fprintf in
    let pex = Print.ex in
    let (vvars,b) = unmbind (mk_free V) funptr in
    let (tvars,b) = unmbind (mk_free T) b in
    let (var,t)   = unbind (mk_free s) (snd b) in
    let vvars = if vs = [||] then [||] else vvars in
    let tvars = if ts = [||] then [||] else tvars in
    let fn ch =
      Array.iteri (fun i v ->
          let t = vs.(i) in
          let sep = if i = 0 then "" else ", " in
          prnt ch "%s%s<-%a" sep (name_of v) VPtr.print t) vvars
    in
    let gn ch =
      Array.iteri (fun i v ->
          let t = ts.(i) in
          let sep = if i = 0 then "" else ", " in
          prnt ch "%s%s<-%a" sep (name_of v) Ptr.print t) tvars
    in
    prnt ch "%s.%a[%t][%t]" (name_of var) pex t fn gn


let print_v_node : out_channel -> v_node -> unit = fun ch n ->
  let prnt = Printf.fprintf in
  let pex = Print.ex in
  match n with
  | VN_LAbs(b)     -> prnt ch "VN_LAbs(%a)" (pbcl V) b
  | VN_Cons(c,pv)  -> prnt ch "VN_Cons(%s,%a)" c.elt VPtr.print pv
  | VN_Reco(m)     -> let pelt ch (k, p) = prnt ch "%S=%a" k VPtr.print p in
                      prnt ch "VN_Reco(%a)" (Print.print_map pelt ":") m
  | VN_Scis        -> prnt ch "VN_Scis"
  | VN_VWit(w)     -> prnt ch "VN_VWit(%a)" pex (Pos.none (VWit(w)))
  | VN_UWit(w)     -> prnt ch "VN_UWit(%a)" pex (Pos.none (UWit(w)))
  | VN_EWit(w)     -> prnt ch "VN_EWit(%a)" pex (Pos.none (EWit(w)))
  | VN_HApp(e)     -> let HO(s,f,a) = e in
                      prnt ch "VN_HApp(%a,%a)" pcl f pcl a
  | VN_UVar(v)     -> prnt ch "VN_UVar(%a)" pex (Pos.none (UVar(V,v)))
  | VN_ITag(n)     -> prnt ch "VN_ITag(%d)" n
  | VN_Goal(v)     -> prnt ch "VN_Goal(%a)" pex v
(** Printing function for term nodes. *)
let print_t_node : out_channel -> t_node -> unit = fun ch n ->
  let prnt = Printf.fprintf in
  let pex = Print.ex in
  match n with
  | TN_Valu(pv)    -> prnt ch "TN_Valu(%a)" VPtr.print pv
  | TN_Appl(pt,pu) -> prnt ch "TN_Appl(%a,%a)" Ptr.print pt Ptr.print pu
  | TN_MAbs(b)     -> prnt ch "TN_MAbs(%a)" (pbcl S) b
  | TN_Name(s,pt)  -> prnt ch "TN_Name(%a,%a)" pex s Ptr.print pt
  | TN_Proj(pv,l)  -> prnt ch "TN_Proj(%a,%s)" VPtr.print pv  l.elt
  | TN_Case(pv,m)  -> let pelt ch (k, b) =
                        prnt ch "%S → %a" k (pbcl V) b
                      in
                      let pmap = Print.print_map pelt "|" in
                      prnt ch "TN_Case(%a|%a)" VPtr.print pv pmap m
  | TN_FixY(b)     -> prnt ch "TN_FixY(%a)" (pbcl T) b
  | TN_Prnt(s)     -> prnt ch "TN_Prnt(%S)" s
  | TN_UWit(w)     -> prnt ch "TN_UWit(%a)" pex (Pos.none (UWit(w)))
  | TN_EWit(w)     -> prnt ch "TN_EWit(%a)" pex (Pos.none (EWit(w)))
  | TN_HApp(e)     -> let HO(s,f,a) = e in
                      prnt ch "TN_HApp(%a,%a)" pcl f pcl a
  | TN_UVar(v)     -> prnt ch "TN_UVar(%a)" pex (Pos.none (UVar(T,v)))
  | TN_ITag(n)     -> prnt ch "TN_ITag(%d)" n
  | TN_Goal(t)     -> prnt ch "TN_Goal(%a)" pex t

(** Type of a pool. *)
type pool =
  { vs       : (VPtr.t * v_node) list
  ; ts       : (TPtr.t * t_node) list
  ; us       : (TPtr.t * t_node) list
  ; next     : int    (** counter to generate new nodes *)
  ; time     : Timed.Time.t (** Current time for references *)
  ; eq_map   : (ptr * ptr) list (* just for printing and debugging *)
  ; values   : (value * v_ptr) list
  }

(**
   Here are some invariants of the pool:

   1°) every Ptr.t is present in the map vs if it is a VPtr.t
       and ts if it is a TPtr.t

   2°) Parents of a node are only significative and searched for
       nodes that have no link in the union-find map (i.e.,
       parents are unused if the node is present in the eq_map).

       TODO #15: this invariant is not enforced by the data structure.

   3°) Term in the pool are kept in normal form. Any update that
       could trigger other normalisation has to be propagated.
       This is the role of the parent node.

       TODO #4: manage update of unification variables
 *)

let funptrs : anyfunptr FunHash.t = FunHash.create 256
let clsptrs : anyclsptr ClsHash.t = ClsHash.create 256

let reset_tbls () =
  Epsilon.reset_epsilons ();
  ClsHash.clear clsptrs;
  FunHash.clear funptrs

(** Printing a pool (useful for debugging. *)
let print_pool : string -> out_channel -> pool -> unit = fun prefix ch po ->
  let { ts; vs; eq_map } = po in
  Printf.fprintf ch "%s#### Nodes ####\n" prefix;
  let fn (k, n) =
    let b = if Timed.get po.time k.Ptr.bs then "*" else "" in
    Printf.fprintf ch "%s  %a%s\t→ %a\t\n" prefix VPtr.print k b
      print_v_node n
  in
  List.iter fn vs;
  Printf.fprintf ch "%s---------------\n" prefix;
  let fn (k, n) =
    let f = if Timed.get po.time k.Ptr.fs then "+" else "" in
    Printf.fprintf ch "%s  %a%s\t→ %a\t\n" prefix TPtr.print k f
      print_t_node n
  in
  List.iter fn ts;
  Printf.fprintf ch "%s#### Links ####\n" prefix;
  let fn (p1, p2) =
    let p3 = ptr_get p1 po.time in
    Printf.fprintf ch "%s  %a\t→ %a (%a)\n" prefix
                   Ptr.print p1 Ptr.print p2 Ptr.print p3
  in
  List.iter fn eq_map;
  Printf.fprintf ch "%s###############" prefix


(** Initial, empty pool. *)
let empty_pool : pool =
  { vs     = []
  ; ts     = []
  ; us     = []
  ; next   = 0
  ; time   = Timed.Time.save ()
  ; eq_map = []
  ; values = []
  }

(** Node search. *)
let find_v_node : VPtr.t -> pool -> v_node = fun p po ->
  let open Ptr in
  match p.vval with
  | DP(V_Node, v) -> v
  | _ -> assert false

let find_t_node : TPtr.t -> pool -> t_node = fun p po ->
  let open Ptr in
  match p.tval with
  | DP(T_Node, v) -> v
  | _ -> assert false

let get_bs : VPtr.t -> pool -> bool = fun p po ->
  let open Ptr in
  Timed.get po.time p.bs

let set_bs : VPtr.t -> pool -> pool = fun p po ->
  let open Ptr in
  { po with time = Timed.set po.time p.bs true }

let get_ns : TPtr.t -> pool -> bool = fun p po ->
  let open Ptr in
  Timed.get po.time p.ns

let set_ns : TPtr.t -> pool -> pool = fun p po ->
  let open Ptr in
  { po with time = Timed.set po.time p.ns true }

let get_fs : TPtr.t -> pool -> bool = fun p po ->
  let open Ptr in
  Timed.get po.time p.fs

let set_fs : TPtr.t -> pool -> pool = fun p po ->
  let open Ptr in
  { po with time = Timed.set po.time p.fs true }

(** Geting the children sons of a node. *)

let children_bndr_closure
    : type a b. (a, b) bndr_closure -> (int -> par_key) ->
           int * (par_key * Ptr.t) list -> int * (par_key * Ptr.t) list
  = fun (_,vs,ts) fn (i0, acc) ->
    let res = ref acc in
    Array.iteri (fun i vptr -> res := (fn (i+i0), Ptr.V_ptr vptr) :: !res) vs;
    let i0 = i0 + Array.length vs in
    Array.iteri (fun i ptr -> res := (fn (i+i0), ptr) :: !res) ts;
    let i0 = i0 + Array.length ts in
    (i0, !res)

let children_closure
    : type a b. a closure -> (int -> par_key) ->
           int * (par_key * Ptr.t) list -> int * (par_key * Ptr.t) list
  = fun (_,vs,ts) fn (i0, acc) ->
    let res = ref acc in
    Array.iteri (fun i vptr -> res := (fn (i+i0), Ptr.V_ptr vptr) :: !res) vs;
    let i0 = i0 + Array.length vs in
    Array.iteri (fun i ptr -> res := (fn (i+i0), ptr) :: !res) ts;
    let i0 = i0 + Array.length ts in
    (i0, !res)

let children_v_node : v_node -> (par_key * Ptr.t) list = fun n ->
  match n with
  | VN_HApp c     -> let HO(_,b,c) = c in
                     let kn n = KV_HApp n in
                     snd (children_closure b kn
                         (children_closure c kn (0, [])))
  | VN_LAbs b     -> let kn n = KV_LAbs n in
                     snd (children_bndr_closure b kn (0, []))
  | VN_Cons(a,pv) -> [(KV_Cons a.elt, Ptr.V_ptr pv)]
  | VN_Reco(m)    -> A.fold (fun a p s -> ((KV_Reco a, Ptr.V_ptr p) :: s)) m []
  | VN_VWit _
  | VN_UWit _
  | VN_EWit _
  | VN_Goal _
  | VN_UVar _ (* TODO #4 check *)
  | VN_ITag _
  | VN_Scis       -> []

let children_t_node : t_node -> (par_key * Ptr.t) list = fun n ->
  match n with
  | TN_Valu(pv)    -> [(KT_Valu, Ptr.V_ptr pv)]
  | TN_Appl(pt,pu) -> [(KT_Appl `Right, pu); (KT_Appl `Left, pt)]
  | TN_Name(_,pt)  -> [(KT_Name, pt)]
  | TN_Proj(pv,l)  -> [(KT_Proj l.elt, Ptr.V_ptr pv)]
  | TN_Case(pv,cs) -> (KT_Case None, Ptr.V_ptr pv) ::
                        A.fold (fun a b acc ->
                            let kn n = KT_Case (Some (a, n)) in
                            snd (children_bndr_closure b kn (0,acc)))
                               cs []
  | TN_FixY(b)     -> let kn n = KT_FixY n in
                      snd (children_bndr_closure b kn (0, []))
  | TN_MAbs b      -> let kn n = KT_MAbs n in
                      snd (children_bndr_closure b kn (0, []))
  | TN_HApp c      -> let HO(_,b,c) = c in
                      let kn n = KT_HApp n in
                      snd (children_closure b kn
                          (children_closure c kn (0,[])))
  | TN_UWit _
  | TN_EWit _
  | TN_Prnt _
  | TN_Goal _
  | TN_UVar _  (* TODO #4 check *)
  | TN_ITag _    -> []

(** Find operation (with path contraction). *)
let find : Ptr.t -> pool -> Ptr.t * pool = fun p po ->
  let rec follow p time =
    try
      let q = ptr_get p time in
      let (r, time) = follow q time in
      let time = if q != r then ptr_set p r time else time in
      (r, time)
    with Not_found -> (p, time)
  in
  let (repr, time) = follow p po.time in
  (repr, {po with time})

let find_valu : VPtr.t -> pool -> VPtr.t * pool = fun p po ->
  let (p, po) = find (Ptr.V_ptr p) po in
  match p with
  | Ptr.V_ptr p -> (p, po)
  | Ptr.T_ptr _ -> assert false

let is_free : Ptr.t -> pool -> bool * pool =
  fun p po ->
    let (p, po) = find p po in
    match p with
    | Ptr.V_ptr _ -> (true, po)
    | Ptr.T_ptr t -> (get_fs t po, po)

let is_nobox : Ptr.t -> pool -> bool * pool =
  fun p po ->
    let (p, po) = find p po in
    match p with
    | Ptr.V_ptr t -> (get_bs t po, po)
    | Ptr.T_ptr _ -> (false, po)

(** Adding a parent to a given node. *)
let add_parent_nodes : Ptr.t -> (par_key * Ptr.t) list-> pool -> pool =
  fun np ps po ->
  let fn po (k, p) =
    let (p, po) = find p po in
    let time = ptr_add_par k np p po.time in
    { po with time }
  in
  List.fold_left fn po ps

let add_parent_v_nodes : VPtr.t -> (par_key * Ptr.t) list -> pool -> pool =
  fun vp ps po -> add_parent_nodes (Ptr.V_ptr vp) ps po

let add_parent_t_nodes : TPtr.t -> (par_key * Ptr.t) list -> pool -> pool =
  fun tp ps po -> add_parent_nodes (Ptr.T_ptr tp) ps po

(** Obtain the parents of a pointed node. *)
let parents : Ptr.t -> pool -> par_map = fun p po ->
  let (p, po) = find p po in
  ptr_par p po.time

let add_parents : Ptr.t -> par_map -> pool -> pool = fun p nps po ->
  let (p, po) = find p po in
  let time = ptr_union_pars nps p po.time in
  { po with time }

(* NOTE: loose path shortening, not really a problem ? *)
let eq_vptr : pool -> VPtr.t -> VPtr.t -> bool = fun po p1 p2 ->
  let (p1, po) = find (Ptr.V_ptr p1) po in
  let (p2, po) = find (Ptr.V_ptr p2) po in
  Ptr.compare p1 p2 = 0

(* NOTE: loose path shortening, not really a problem ? *)
let eq_tptr : pool -> TPtr.t -> TPtr.t -> bool = fun po p1 p2 ->
  let (p1, po) = find (Ptr.T_ptr p1) po in
  let (p2, po) = find (Ptr.T_ptr p2) po in
  Ptr.compare p1 p2 = 0

(* NOTE: loose path shortening, not really a problem ? *)
let eq_ptr : pool -> Ptr.t -> Ptr.t -> bool = fun po p1 p2 ->
  let (p1, po) = find p1 po in
  let (p2, po) = find p2 po in
  eq_ptr p1 p2

let eq_ho_appl : type a. pool -> a ho_appl -> a ho_appl -> bool =
  fun po a1 a2 ->
    let open Eq in
    let (HO(s1,(f1,vf1,tf1),(e1,ve1,te1)),
         HO(s2,(f2,vf2,tf2),(e2,ve2,te2))) = (a1, a2) in
    match eq_sort s1 s2 with
    | Eq ->
       f1 == f2 && e1 == e2 &&
         Array.for_all2 (eq_vptr po) vf1 vf2 &&
           Array.for_all2 (eq_ptr po) tf1 tf2 &&
             Array.for_all2 (eq_vptr po) ve1 ve2 &&
               Array.for_all2 (eq_ptr po) te1 te2
    | NEq -> false

let eq_cl po s (f1,vs1,ts1 as _cl1) (f2,vs2,ts2 as _cl2) =
  if f1 == f2 then
    Array.for_all2 (eq_vptr po) vs1 vs2 &&
    Array.for_all2 (eq_ptr  po) ts1 ts2
  else
    ((*assert (not (eq_funptr s f1 f2) ||
               (Printf.eprintf "%a (%d)\n%a (%d)\n%!"
                               (pbcl s) _cl1 (hash_funptr s f1)
                               (pbcl s) _cl2 (hash_funptr s f2);
                false);*)
     false)

(** Equality functions on nodes. *)
let eq_v_nodes : pool -> v_node -> v_node -> bool =
  fun po n1 n2 -> n1 == n2 ||
    match (n1, n2) with
    | (VN_LAbs(b1)   , VN_LAbs(b2)   ) -> eq_cl po V b1 b2
    | (VN_Cons(c1,p1), VN_Cons(c2,p2)) -> c1.elt = c2.elt && eq_vptr po p1 p2
    | (VN_Reco(m1)   , VN_Reco(m2)   ) -> A.equal (eq_vptr po) m1 m2
    | (VN_Scis       , VN_Scis       ) -> true
    | (VN_VWit(w1)   , VN_VWit(w2)   ) -> w1.valu == w2.valu
    | (VN_UWit(w1)   , VN_UWit(w2)   ) -> w1.valu == w2.valu
    | (VN_EWit(w1)   , VN_EWit(w2)   ) -> w1.valu == w2.valu
    | (VN_ITag(n1)   , VN_ITag(n2)   ) -> n1 = n2
    | (VN_HApp(e1)   , VN_HApp(e2)   ) -> eq_ho_appl po e1 e2
    | (VN_Goal(v1)   , VN_Goal(v2)   ) -> eq_expr v1 v2
    | (VN_UVar(v1)   , VN_UVar(v2)   ) -> v1.uvar_key = v2.uvar_key
    | (_             , _             ) -> false

let eq_t_nodes : pool -> t_node -> t_node -> bool =
  fun po n1 n2 -> n1 == n2 ||
    match (n1, n2) with
    | (TN_Valu(p1)     , TN_Valu(p2)     ) -> eq_vptr po p1 p2
    | (TN_Appl(p11,p12), TN_Appl(p21,p22)) -> eq_ptr po p11 p21
                                              && eq_ptr po p12 p22
    | (TN_MAbs(b1)     , TN_MAbs(b2)     ) -> eq_cl po S b1 b2
    | (TN_Name(s1,p1)  , TN_Name(s2,p2)  ) -> eq_expr s1 s2
                                              && eq_ptr po p1 p2
    | (TN_Proj(p1,l1)  , TN_Proj(p2,l2)  ) -> eq_vptr po p1 p2
                                              && l1.elt = l2.elt
    | (TN_Case(p1,m1)  , TN_Case(p2,m2)  ) -> eq_vptr po p1 p2
                                              && A.equal (eq_cl po V) m1 m2
    | (TN_FixY(b1)     , TN_FixY(b2)     ) -> eq_cl po Sorts.T b1 b2
    | (TN_Prnt(s1)     , TN_Prnt(s2)     ) -> s1 = s2
    | (TN_UWit(w1)     , TN_UWit(w2)     ) -> w1.valu == w2.valu
    | (TN_EWit(w1)     , TN_EWit(w2)     ) -> w1.valu == w2.valu
    | (TN_ITag(n1)     , TN_ITag(n2)     ) -> n1 = n2
    | (TN_HApp(e1)     , TN_HApp(e2)     ) -> eq_ho_appl po e1 e2
    | (TN_Goal(t1)     , TN_Goal(t2)     ) -> eq_expr t1 t2
    | (TN_UVar(v1)     , TN_UVar(v2)     ) -> v1.uvar_key = v2.uvar_key
    | (_               , _               ) -> false


let immediate_nobox : v_node -> bool = function
  | VN_LAbs _
  | VN_Cons _
  | VN_Reco _
  | VN_Scis   -> true (* Check VN_Scis *)
  | VN_VWit _
  | VN_UWit _
  | VN_EWit _
  | VN_HApp _
  | VN_UVar _
  | VN_Goal _
  | VN_ITag _ -> false

(** Insertion function for nodes. *)
exception FoundV of VPtr.t * pool
let insert_v_node : v_node -> pool -> VPtr.t * pool = fun nn po ->
  let children = children_v_node nn in
  try
    match children with
    | [] ->
       let fn (p, n) = if eq_v_nodes po n nn then raise (FoundV (p,po)) in
       List.iter fn po.vs; raise Not_found
    | (k,n)::l ->
       let f k n = MapKey.find k (parents n po) in
       let possible =
         List.fold_left (fun acc (k, n) -> PtrSet.inter (f k n) acc) (f k n) l
       in
       let rec fn po n = match n with
         | Ptr.V_ptr n ->
            let node = find_v_node n po in
            if eq_v_nodes po node nn then raise (FoundV (n,po))
         | Ptr.T_ptr n -> ()
       in
       PtrSet.iter (fn po) possible;
       raise Not_found
  with
  | FoundV(p,po) -> (p, po)
  | Not_found ->
     let open Ptr in
     let ptr = { vadr = po.next
               ; vlnk = Timed.tref (Par MapKey.empty)
               ; bs   = Timed.tref (immediate_nobox nn)
               ; vval = DP(V_Node, nn) } in
     let vs = (ptr,nn) :: po.vs in
     let next = po.next + 1 in
     let po = { po with vs ; next } in
     let po = add_parent_v_nodes ptr children po in
     (ptr, po)

exception FoundT of TPtr.t * pool

let insert_t_node : bool -> t_node -> pool -> TPtr.t * pool =
  fun fs nn po ->
    let children = children_t_node nn in
    try
      match children with
      | [] ->
         let fn (p, n) = if eq_t_nodes po n nn then raise (FoundT (p,po)) in
         List.iter fn po.ts; raise Not_found
      | (k,n)::l ->
         let f k n = MapKey.find k (parents n po) in
         let possible =
           List.fold_left (fun acc (k,n) -> PtrSet.inter (f k n) acc) (f k n) l
         in
         let rec fn po n = match n with
           | Ptr.V_ptr _ -> ()
           | Ptr.T_ptr n ->
              let node = find_t_node n po in
              if eq_t_nodes po node nn then raise (FoundT (n,po));
         in
         PtrSet.iter (fn po) possible;
         raise Not_found
    with
    | FoundT(p, po) ->
       let po =
         if fs then begin
             let (p', po) = find (Ptr.T_ptr p) po in
             match p' with
             | Ptr.T_ptr p' -> set_fs p' po
             | _ -> po
           end
         else po
       in (p, po)
    | Not_found ->
       let open Ptr in
       let ptr = { tadr = po.next
                 ; tlnk = Timed.tref (Par MapKey.empty)
                 ; ns   = Timed.tref false
                 ; fs   = Timed.tref fs
                 ; tval = DP(T_Node, nn) } in
       let ts = (ptr, nn) :: po.ts in
       let time, eq_map =
         match nn with
        | TN_Valu(pv) -> let tp = Ptr.T_ptr ptr and vp = Ptr.V_ptr pv in
                         (ptr_set tp vp po.time, (tp,vp)::po.eq_map)
        | _           -> (po.time, po.eq_map)
       in
       let next= po.next + 1 in
       let po = { po with time; ts ; next; eq_map } in
       let po = add_parent_t_nodes ptr children po in
       (ptr, po)

let insert_v_node nn po = Chrono.add_time inser_chrono (insert_v_node nn) po
let insert_t_node nn po = Chrono.add_time inser_chrono (insert_t_node nn) po

(** Insertion of actual terms and values to the pool. *)
    (* safe means no VPtr/TPtr are in the term *)
let rec add_term :  bool -> bool -> pool -> term -> Ptr.t * pool =
  fun free safe po t ->
  let add_term = add_term free safe in
  let add_valu = add_valu safe in
  let insert node po =
    if free then normalise_t_node node po
    else let (p, po) = insert_t_node false node po in find (Ptr.T_ptr p) po
  in
  log2 "add_term %b %a" free Print.ex t;
  let t = Norm.whnf t in
  match t.elt with
  | Valu(v)     -> let (pv, po) = add_valu po v in
                   insert (TN_Valu(pv)) po
  | Appl(t,u)   -> let (pt, po) = add_term po t in
                   let (pu, po) = add_term po u in
                   insert (TN_Appl(pt,pu)) po
  | MAbs(b)     -> let (cl, po) = add_bndr_closure po safe S T b in
                   insert (TN_MAbs(cl)) po
  | Name(s,t)   -> let (pt, po) = add_term po t in
                   insert (TN_Name(s,pt)) po
  | Proj(v,l)   -> let (pv, po) = add_valu po v in
                   insert (TN_Proj(pv,l)) po
  | Case(v,m)   -> let (pv, po) = add_valu po v in
                   let (m,  po) = A.fold_map
                       (fun _ (_,x) po -> add_bndr_closure po safe V T x) m po
                   in
                   insert (TN_Case(pv,m)) po
  | FixY(b)     -> let (cl, po) = add_bndr_closure po safe T V b in
                   let (pt, po) = insert_t_node false (TN_FixY(cl)) po in
                   normalise (Ptr.T_ptr pt) po
  | Prnt(s)     -> insert (TN_Prnt(s)) po
  | Repl(_,u,_) -> add_term po u
  | Coer(_,t,_) -> add_term po t
  | Such(_,_,r) -> add_term po (bseq_dummy r.binder)
  | UWit(w)     -> insert (TN_UWit(w)) po
  | EWit(w)     -> insert (TN_EWit(w)) po
  | HApp(s,f,a) -> let (hoa, po) = add_ho_appl safe po s f a in
                   insert (TN_HApp(hoa)) po
  | HDef(_,d)   -> add_term po d.expr_def
  | UVar(_,v)   -> insert (TN_UVar(v)) po
  | ITag(_,n)   -> insert (TN_ITag(n)) po
  | Goal(_)     -> insert (TN_Goal(t)) po
  | TPtr(pt)    -> if free then normalise pt po else find pt po
  | Vari(_)     -> invalid_arg "free variable in the pool"
  | Dumm(_)     -> invalid_arg "dummy terms forbidden in the pool"

and     add_valu : bool -> pool -> valu -> VPtr.t * pool = fun safe po v ->
  let add_valu = add_valu safe in
  let v = Norm.whnf v in
  match v.elt with
  | LAbs(_,b)   -> let (b, po) = add_bndr_closure po safe V T b in
                   insert_v_node (VN_LAbs(b)) po
  | Cons(c,v)   -> let (pv, po) = add_valu po v in
                   insert_v_node (VN_Cons(c,pv)) po
  | Reco(m)     -> let fn l (_, v) (m, po) =
                     let (pv, po) = add_valu po v in
                     (A.add l pv m, po)
                   in
                   let (m, po) = A.fold fn m (A.empty, po) in
                   insert_v_node (VN_Reco(m)) po
  | Scis        -> insert_v_node VN_Scis po
  | VDef(d)     -> begin
(*                     try
                       let pv = List.assq d po.values in
                       Printf.eprintf "reuse %a\n%!" VPtr.print pv;
                       (pv, po)
                     with Not_found ->*)
                       let (pv,po) = add_valu po d.value_eras in
                       (*Printf.eprintf "valu create %a\n%!" VPtr.print pv;*)
                       let po = { po with values = (d,pv)::po.values } in
                       (pv, po)
                   end
  | Coer(_,v,_) -> add_valu po v
  | Such(_,_,r) -> add_valu po (bseq_dummy r.binder)
  | VWit(w)     -> insert_v_node (VN_VWit(w)) po
  | UWit(w)     -> insert_v_node (VN_UWit(w)) po
  | EWit(w)     -> insert_v_node (VN_EWit(w)) po
  | HApp(s,f,a) -> let (hoa, po) = add_ho_appl safe po s f a in
                   insert_v_node (VN_HApp(hoa)) po
  | HDef(_,d)   -> add_valu po d.expr_def
  | UVar(_,v)   -> insert_v_node (VN_UVar(v)) po
  | ITag(_,n)   -> insert_v_node (VN_ITag(n)) po
  | Goal(_)     -> insert_v_node (VN_Goal(v)) po
  | VPtr(pv)    -> (pv, po)
  | Vari(_)     -> invalid_arg "free variable in the pool"
  | Dumm(_)     -> invalid_arg "dummy terms forbidden in the pool"

and add_bndr_closure : type a b. pool -> bool -> a sort -> b sort ->
                       (a, b) bndr -> (a, b) bndr_closure * pool =
  fun po safe sa sr b ->
    let (funptr, vs, ts as cl) = Misc.make_bndr_closure safe sa b in
    let po = ref po in
    let vs = Array.map (fun v -> let (vptr,p) = add_valu safe !po v in
                                 po := p; vptr) vs
    in
    let ts = Array.map (fun t -> let (tptr,p) = add_term false safe !po t in
                                 po := p; tptr) ts
    in
    let po = !po in
    let key = T(sa,sr,funptr) in
    (*print_pool "TEST" stderr po;*)
    try
      let T(sa',sr',funptr') = FunHash.find funptrs key in
      match eq_sort sa sa', eq_sort sr sr' with
      | Eq.Eq, Eq.Eq -> ((funptr',vs,ts), po)
      | _ -> assert false
    with Not_found ->
      FunHash.add  funptrs key key;
      ((funptr,vs,ts), po)

and add_ho_appl
    : type a b. bool -> pool -> a sort -> (a -> b) ex loc
           -> a ex loc -> b ho_appl * pool
  = fun safe po se f e ->
    let (sf, f) = sort f in
    let (f, vf, tf as cf) = Misc.make_closure f in
    let (e, ve, te as ce) = Misc.make_closure e in
    let po = ref po in
    let vf = Array.map (fun v -> let (vptr,p) = add_valu safe !po v in
                                 po := p; vptr) vf
    in
    let tf = Array.map (fun t -> let (ptr,p) = add_term false safe !po t in
                                 po := p; ptr) tf
    in
    let ve = Array.map (fun v -> let (vptr,p) = add_valu safe !po v in
                                 po := p; vptr) ve
    in
    let te = Array.map (fun t -> let (ptr,p) = add_term false safe !po t in
                                 po := p; ptr) te
    in
    let po = !po in
    let key = C(sf, f) in
    let f : unit -> (a -> b) clsptr = fun () ->
      try
        let C(sf',f') = ClsHash.find clsptrs key in
        match eq_sort sf sf' with
        | Eq.Eq -> f'
        | _ -> assert false
      with Not_found ->
        ClsHash.add clsptrs key key;
        f
    in
    let key = C(se,e) in
    let e : unit -> a clsptr = fun () ->
      try
        let C(se',e') = ClsHash.find clsptrs key in
        match eq_sort se se' with
        | Eq.Eq -> e'
        | _ -> assert false
      with Not_found ->
        ClsHash.add clsptrs key key;
        e
    in
    (HO(se,(f (),vf,tf),(e (),ve,te)), po)

(** Normalisation function. *)
and normalise : Ptr.t -> pool -> Ptr.t * pool =
  fun p0 po ->
    match p0 with
    | Ptr.V_ptr _ -> (p0, po)
    | Ptr.T_ptr p ->
       if get_ns p po then
         find p0 po
       else
         begin
           let (tp, po) = normalise_t_node ~old:p (find_t_node p po) po in
           let po = union (Ptr.T_ptr p) tp po in
           find tp po
         end

and normalise_t_node : ?old:TPtr.t -> t_node -> pool -> Ptr.t  * pool =
  fun ?old node po ->
    let insert node po =
      match old with
      | None   -> let (p, po) = insert_t_node true node po in
                  find (Ptr.T_ptr p) po
      | Some p -> find (Ptr.T_ptr p) po
    in
    let set_ns po =
      match old with
      | None   -> po
      | Some p -> set_ns p po
    in
    let (p, po) = match node with
      | TN_Valu(pv)    -> let po = set_ns po in
                          find (Ptr.V_ptr pv) po
      | TN_Appl(pt,pu) ->
         begin
           log2 "normalise in %a = TN_Appl: %a %a"
                print_t_node node Ptr.print pt Ptr.print pu;
           let (pt, po) = normalise pt po in
           let (pu, po) = normalise pu po in
           try match (pt, pu) with
           | (Ptr.V_ptr pf, Ptr.V_ptr pv) ->
              begin
                match find_v_node pf po, get_bs pv po with
                | VN_LAbs(b), true        ->
                   begin
                     let b = subst_closure b in
                     let t = bndr_subst b (VPtr pv) in
                     let po = set_ns po in
                     let (tp, po) = add_term true false po t in
                     log2 "normalised in %a = TN_Appl Lambda %a %a => %a"
                          print_t_node node Ptr.print pt Ptr.print pu
                          Ptr.print tp;
                     (tp,po)
                   end
                | _          ->
                   raise Exit
              end
           | (_           , _           ) -> raise Exit
           with Exit ->
              let (tp, po) = insert (TN_Appl(pt,pu)) po in
               (* NOTE: testing tp in po.ns seems incomplete *)
              log2 "normalised in %a = TN_Appl: %a %a => %a"
                   print_t_node node Ptr.print pt Ptr.print pu Ptr.print tp;
              (tp, po)
         end
      | TN_MAbs(b)     -> insert node po (* FIXME #7 can do better. *)
      | TN_Name(s,pt)  -> insert node po (* FIXME #7 can do better. *)
      | TN_Proj(pv0,l) ->
         begin
           let (pv, po) = find_valu pv0 po in
           log2 "normalisation in %a = TN_Proj %a"
                print_t_node node VPtr.print pv0;
           match find_v_node pv po with
           | VN_Reco(m) ->
              begin
                try
                  let (tp, po) = find (Ptr.V_ptr (A.find l.elt m)) po in
                  let po = set_ns po in
                  log2 "normalised in %a = TN_Proj %a => %a"
                       print_t_node node VPtr.print pv0 Ptr.print tp;
                  (tp, po)
                with Not_found -> insert node po
              end
           | _          -> insert node po
         end
      | TN_Case(pv0,m) ->
         begin
           let (pv, po) = find_valu pv0 po in
           log2 "normalisation in %a = TN_Case %a"
                print_t_node node VPtr.print pv0;
           try
             match find_v_node pv po with
             | VN_Cons(c,pv) ->
                let b = subst_closure (A.find c.elt m) in
                let t = bndr_subst b (VPtr pv) in
                let po = set_ns po in
                let (tp, po) = add_term true false po t in
                log2 "normalised in %a = TN_Case %a => %a"
                     print_t_node node VPtr.print pv0 Ptr.print tp;
                (tp,po)
             | _            -> raise Not_found
           with Not_found ->
             log2 "normalisation no progress %a = TN_Case: %a"
                  print_t_node node VPtr.print pv0;
             insert node po
         end
      | TN_FixY(f) ->
         begin
           log2 "normalisation in TN_FixY: %a" print_t_node node;
           let po = set_ns po in
           let b = subst_closure f in
           let (pv, po) = add_valu false po (bndr_subst b (FixY(b))) in
           log2 "normalised in TN_FixY: %a => %a"  print_t_node node
                VPtr.print pv;
           find (Ptr.V_ptr pv) po
         end
      | TN_UVar(v)   ->
         begin
           match !(v.uvar_val) with
           | Unset _ -> insert node po
           | Set t   -> let po = set_ns po in
                        add_term true true po t
         end
      | TN_Prnt(_)
      | TN_UWit(_)
      | TN_EWit(_)
      | TN_HApp(_)
      | TN_Goal(_)
      | TN_ITag(_)    -> let po = set_ns po in
                         insert node po
    in
    find p po

and check_eq : Ptr.t -> Ptr.t -> pool -> pool = fun p1 p2 po ->
  if eq_ptr po p1 p2 then po else
    match (p1, p2) with
    | Ptr.V_ptr vp1, Ptr.V_ptr vp2 ->
       let n1 = find_v_node vp1 po in
       let n2 = find_v_node vp2 po in
       if eq_v_nodes po n1 n2 then union p1 p2 po else po
    | Ptr.T_ptr tp1, Ptr.T_ptr tp2 ->
       let n1 = find_t_node tp1 po in
       let n2 = find_t_node tp2 po in
       if eq_t_nodes po n1 n2 then union p1 p2 po else po
    | _ -> po

and check_parents_eq pp1 pp2 po =
  let po = ref po in
  let fn k pp1 pp2 = match (pp1, pp2) with
    | (Some pp1, Some pp2) ->
       po := PtrSet.fold (fun p1 po ->
                 PtrSet.fold (fun p2 po ->
                     check_eq p1 p2 po) pp2 po) pp1 !po;
       None
    | ( _      , _       ) -> None
  in
  Chrono.add_time pareq_chrono
                  (fun () -> ignore (MapKey.merge fn pp1 pp2); !po) ()

and reinsert : Ptr.t -> pool -> pool = fun p po ->
  let (is_free, po) = is_free p po in
  match p with
  | Ptr.T_ptr tp ->
     if is_free then snd (normalise (Ptr.T_ptr tp) po) else po
  | Ptr.V_ptr vp ->
     let n1 = find_v_node vp po in
     begin
       match n1 with
       | VN_UVar({uvar_val = {contents = Set v}}) ->
          let (vp,po) = add_valu true po v in
          union p (Ptr.V_ptr vp) po
       | _ -> po
     end

(** Union operation. *)
and join : Ptr.t -> Ptr.t -> pool -> pool = fun p1 p2 po ->
  assert (not_lnk p1 po.time);
  assert (not_lnk p2 po.time);
  let nps = parents p1 po in
  let pp2 = parents p2 po in
  let po = { po with time = ptr_set p1 p2 po.time
                   ; eq_map = (p1,p2) :: po.eq_map }
  in
  let po = check_parents_eq nps pp2 po in
  let (bs2, po) = is_nobox p2 po in
  let (bs1, po) = is_nobox p1 po in
  let po = if bs1 && not bs2 then begin
               match p2 with
               | Ptr.V_ptr p2 -> set_bs p2 po
               | Ptr.T_ptr _  -> assert false
             end
           else po
  in
  let (fs2, po) = is_free p2 po in
  let (fs1, po) = is_free p1 po in
  let po = if fs1 && not fs2 then begin
               match p2 with
               | Ptr.T_ptr p2 -> set_fs p2 po
               | Ptr.V_ptr _  -> assert false
             end
           else po
  in
  let po = MapKey.fold (fun k l po ->
               if is_head k then PtrSet.fold reinsert l po else po) nps po in
  let po = add_parents p2 nps po in
  po

(* when the join can be arbitrary, better to point to
   the oldest pointer (likely to given less occur-check failure*)
and age_join : Ptr.t -> Ptr.t -> pool -> pool = fun p1 p2 po ->
  if p2 < p1 then join p1 p2 po else join p2 p1 po

and union : ?no_rec:bool -> Ptr.t -> Ptr.t -> pool -> pool =
  fun ?(no_rec=false) p1 p2 po ->
  let (p1, po) = find p1 po in
  let (p2, po) = find p2 po in
  if eq_ptr po p1 p2 then po else
    match (p1, p2) with
    | (Ptr.T_ptr _  , Ptr.V_ptr _  ) -> join p1 p2 po
    | (Ptr.V_ptr _  , Ptr.T_ptr _  ) -> join p2 p1 po
    | (Ptr.T_ptr _  , Ptr.T_ptr _  ) -> age_join p1 p2 po
    | (Ptr.V_ptr vp1, Ptr.V_ptr vp2) ->
       begin
         let n1 = find_v_node vp1 po in
         let n2 = find_v_node vp2 po in
         match (n1, n2) with
         (* Immediate contradictions. *)
         | (VN_LAbs(_)     , VN_Reco(_)     )
           | (VN_LAbs(_)     , VN_Cons(_,_)   )
           | (VN_Reco(_)     , VN_LAbs(_)     )
           | (VN_Reco(_)     , VN_Cons(_,_)   )
           | (VN_Cons(_,_)   , VN_Reco(_)     )
           | (VN_Cons(_,_)   , VN_LAbs(_)     ) -> bottom ()
         (* Constructors. *)
         | (VN_Cons(c1,vp1), VN_Cons(c2,vp2)) ->
            if c1.elt <> c2.elt then bottom ();
            let po = age_join p1 p2 po in
            if no_rec then po else union (Ptr.V_ptr vp1) (Ptr.V_ptr vp2) po
         (* Records. *)
         | (VN_Reco(m1)    , VN_Reco(m2)    ) ->
            let po = ref (age_join p1 p2 po) in
            let test vp1 vp2 =
              po := union (Ptr.V_ptr vp1) (Ptr.V_ptr vp2) !po; true
            in
            if not no_rec && not (A.equal test m1 m2) then bottom ();
            !po
         (* Prefer real values as equivalence class representatives. *)
         | (VN_LAbs(_)     , VN_LAbs(_)     ) -> age_join p1 p2 po
         | (VN_LAbs(_)     , _              )     (* FIXME #22 *)
         | (VN_Reco(_)     , _              )
         | (VN_Cons(_,_)   , _              ) -> join p2 p1 po
         | (_              , VN_LAbs(_)     )
         | (_              , VN_Reco(_)     )
         | (_              , VN_Cons(_,_)   ) -> join p1 p2 po
         (* nobox or age_join otherwise. *)
         | (_              , _              ) ->
            match (get_bs vp1 po, get_bs vp2 po) with
            | (true, false) -> join p2 p1 po
            | (false, true) -> join p1 p2 po
            | (_    , _   ) -> age_join p2 p1 po
       end

(** Obtain the canonical term / value pointed by a pointer. *)
(* NOTE: the "clos" bool is here to not follow the union find map if
    under closure, otherwise if loops, for instance on "exp n" *)
let rec canonical_term : bool -> TPtr.t -> pool -> term * pool
  = fun clos p po ->
  let (p, po) = if clos then (Ptr.T_ptr p,po) else find (Ptr.T_ptr p) po in
  let cv = canonical_valu clos in
  let cp = canonical      clos in
  match p with
  | Ptr.T_ptr(p) ->
     begin
        let t = find_t_node p po in
        (*log2 "canonical_term %a = %a" TPtr.print p print_t_node t;*)
        match t with
        | TN_Valu(pv)    -> let (v, po) = cv pv po in
                            (Pos.none (Valu(v)), po)
        | TN_Appl(pt,pu) -> let (t, po) = cp pt po in
                            let (u, po) = cp pu po in
                            (Pos.none (Appl(t,u)), po)
        | TN_MAbs(b)     -> let (b, po) = canonical_bndr_closure b po in
                            (Pos.none (MAbs(b)), po)
        | TN_Name(s,pt)  -> let (t, po) = cp pt po in
                            (Pos.none (Name(s,t)), po)
        | TN_Proj(pv,l)  -> let (v, po) = cv pv po in
                            (Pos.none (Proj(v,l)), po)
        | TN_Case(pv,m)  -> let (v, po) = cv pv po in
                            let (m, po) = A.fold_map (fun _ b po ->
                              let (p, po) = canonical_bndr_closure b po in
                              ((None, p), po)) m po
                            in
                            (Pos.none (Case(v, m)), po)
        | TN_FixY(b)     -> let (b, po) = canonical_bndr_closure b po in
                            (Pos.none (FixY(b)), po)
        | TN_Prnt(s)     -> (Pos.none (Prnt(s)), po)
        | TN_UWit(w)     -> (Pos.none (UWit(w)), po)
        | TN_EWit(w)     -> (Pos.none (EWit(w)), po)
        | TN_HApp(e)     -> let HO(s,f,a) = e in
                            let (f, po) = canonical_closure f po in
                            let (a, po) = canonical_closure a po in
                            (Pos.none (HApp(s,f,a)), po)
        | TN_UVar(v)     -> begin
                              match !(v.uvar_val) with
                              | Unset _ -> (Pos.none (UVar(T,v)), po)
                              | Set t   ->
                                  let (tp, po) = add_term false true po t in
                                  let po = union (Ptr.T_ptr p) tp po in
                                  cp tp po
                            end
        | TN_ITag(n)     -> (Pos.none (ITag(T,n)), po)
        | TN_Goal(t)     -> (t, po)
      end
  | Ptr.V_ptr(p) ->
      let (v, po) = cv p po in
      (Pos.none (Valu(v)), po)

(* NOTE: the "clos" bool is here to not follow the union find map if
    under closure, otherwise if loops, for instance on "exp n" *)
and     canonical_valu : bool -> VPtr.t -> pool -> valu * pool
= fun clos p po ->
  let (p, po) = if clos then (Ptr.V_ptr p, po) else find (Ptr.V_ptr p) po in
  let cv = canonical_valu clos in
  match p with
  | Ptr.T_ptr(p) -> assert false (* Should never happen. *)
  | Ptr.V_ptr(p) ->
      begin
        let v = find_v_node p po in
        (*log2 "canonical_term %a = %a" VPtr.print p print_v_node v;*)
        match v with
        | VN_LAbs(b)     -> let (b, po) = canonical_bndr_closure b po in
                            (Pos.none (LAbs(None, b)), po)
        | VN_Cons(c,pv)  -> let (v, po) = cv pv po in
                            (Pos.none (Cons(c,v)), po)
        | VN_Reco(m)     -> let fn l pv (m, po) =
                              let (v, po) = cv pv po in
                              (A.add l (None,v) m, po)
                            in
                            let (m, po) = A.fold fn m (A.empty, po) in
                            (Pos.none (Reco(m)), po)
        | VN_Scis        -> (Pos.none Scis, po)
        | VN_VWit(w)     -> (Pos.none (VWit(w)), po)
        | VN_UWit(w)     -> (Pos.none (UWit(w)), po)
        | VN_EWit(w)     -> (Pos.none (EWit(w)), po)
        | VN_HApp(e)     -> let HO(s,f,a) = e in
                            let (f, po) = canonical_closure f po in
                            let (a, po) = canonical_closure a po in
                            (Pos.none (HApp(s,f,a)), po)
        | VN_UVar(v)     -> begin
                              match !(v.uvar_val) with
                              | Unset _ -> (Pos.none (UVar(V,v)), po)
                              | Set w   ->
                                 let (vp, po) = add_valu true po w in
                                 let po = union (Ptr.V_ptr p)
                                                (Ptr.V_ptr vp) po
                                 in
                                 cv vp po
                            end
        | VN_ITag(n)     -> (Pos.none (ITag(V,n)), po)
        | VN_Goal(v)     -> (v, po)

      end

and canonical_closure: type a. a closure -> pool -> a ex loc * pool =
  fun (clsptr,vs,ts) po ->
    let po = ref po in
    let vs = Array.map (fun p -> let (p, po') = canonical_valu true p !po in
                                 po := po'; p.elt) vs
    in
    let ts = Array.map (fun p -> let (p, po') = canonical true p !po in
                                 po := po'; p.elt) ts
    in
    (msubst (msubst clsptr vs) ts, !po)

and canonical_bndr_closure : type a b.(a,b) bndr_closure -> pool
                                  -> (a,b) bndr * pool =
  fun (funptr,vs,ts) po ->
    let po = ref po in
    let vs = Array.map (fun p -> let (p, po') = canonical_valu true p !po in
                                 po := po'; p.elt) vs
    in
    let ts = Array.map (fun p -> let (p, po') = canonical true p !po in
                                 po := po'; p.elt) ts
    in
    (msubst (msubst funptr vs) ts, !po)

and canonical : bool -> Ptr.t -> pool -> term * pool = fun clos p po ->
  match p with
  | Ptr.T_ptr p -> canonical_term clos p po
  | Ptr.V_ptr p -> let (v, po) = canonical_valu clos p po in
                   (Pos.none (Valu v), po)


let canonical_valu = canonical_valu false
let canonical_term = canonical_term false
let canonical      = canonical      false

exception NoUnif

let rec unif_cl
        : type a b.pool -> a sort -> (a,b) bndr_closure
                                  -> (a,b) bndr_closure -> pool =
  fun po s (f1,vs1,ts1) (f2,vs2,ts2 ) ->
    let po = ref po in
    if f1 == f2 then
      begin
        Array.iter2 (fun v1 v2 -> po := unif_vptr !po v1 v2) vs1 vs2;
        Array.iter2 (fun t1 t2 -> po := unif_ptr  !po t1 t2) ts1 ts2;
        !po
      end
    else
      raise NoUnif

(* NOTE: loose path shortening, not really a problem ? *)
and unif_vptr : pool -> VPtr.t -> VPtr.t -> pool = fun po p1 p2 ->
  unif_ptr po (Ptr.V_ptr p1) (Ptr.V_ptr p2)

(* NOTE: loose path shortening, not really a problem ? *)
and unif_tptr : pool -> TPtr.t -> TPtr.t -> pool = fun po p1 p2 ->
  unif_ptr po (Ptr.T_ptr p1) (Ptr.T_ptr p2)

and unif_ptr : pool -> Ptr.t -> Ptr.t -> pool = fun po p1 p2 ->
  let (p1, po) = find p1 po in
  let (p2, po) = find p2 po in
  if eq_ptr po p1 p2 then po else
  match p1, p2 with
  | (Ptr.V_ptr vp1, Ptr.V_ptr vp2) ->
     let v1 = find_v_node vp1 po in
     let v2 = find_v_node vp2 po in
     unif_v_nodes po vp1 v1 vp2 v2
  | (Ptr.T_ptr tp1, Ptr.T_ptr tp2) ->
     let v1 = find_t_node tp1 po in
     let v2 = find_t_node tp2 po in
     unif_t_nodes po tp1 v1 tp2 v2
  | (Ptr.T_ptr p1, Ptr.V_ptr p2) ->
     let t1 = find_t_node p1 po in
     begin
       match t1 with
       | TN_UVar v ->
          let (p, po) = canonical_valu p2 po in
          if uvar_occurs v p then raise NoUnif;
          uvar_set v (Pos.none (Valu p));
          union (Ptr.T_ptr p1) (Ptr.V_ptr p2) po
       | _ -> raise NoUnif
     end
  | (Ptr.V_ptr p1, Ptr.T_ptr p2) ->
     let t2 = find_t_node p2 po in
     begin
       match t2 with
       | TN_UVar v ->
          let (p, po) = canonical_valu p1 po in
          if uvar_occurs v p then raise NoUnif;
          uvar_set v (Pos.none (Valu p));
          union (Ptr.T_ptr p2) (Ptr.V_ptr p1) po
       | _ -> raise NoUnif
     end

and unif_expr : type a.pool -> a ex loc -> a ex loc -> pool =
  fun po e1 e2 ->
    let po = ref po in
    if eq_expr ~oracle:(oracle po) ~strict:false e1 e2 then !po
    else raise NoUnif

and unif_bndr: type a b. pool -> a sort -> (a,b) bndr -> (a,b) bndr -> pool =
  fun po s e1 e2 ->
    let po = ref po in
    if eq_bndr ~oracle:(oracle po) ~strict:false s e1 e2 then !po
    else raise NoUnif

and unif_ho_appl : type a. pool -> a ho_appl -> a ho_appl -> pool =
  fun po a1 a2 ->
    let open Eq in
    let (HO(s1,(f1,vf1,tf1),(e1,ve1,te1)),
         HO(s2,(f2,vf2,tf2),(e2,ve2,te2))) = (a1, a2) in
    match eq_sort s1 s2 with
    | Eq ->
       if f1 == f2 && e1 == e2 then
         begin
           let po = Array.fold_left2 unif_vptr po vf1 vf2 in
           let po = Array.fold_left2 unif_ptr  po tf1 tf2 in
           let po = Array.fold_left2 unif_vptr po ve1 ve2 in
           let po = Array.fold_left2 unif_ptr  po te1 te2 in
           po
         end
       else raise NoUnif
    | NEq -> raise NoUnif

(** Equality functions on nodes. *)
and unif_v_nodes : pool -> VPtr.t -> v_node -> VPtr.t -> v_node -> pool =
  fun po p1 n1 p2 n2 -> if n1 == n2 then po else begin
    match (n1, n2) with
    | (VN_UVar({uvar_val = {contents = Set v}}), _) ->
       let po = reinsert (Ptr.V_ptr p1) po in
       unif_vptr po p1 p2
    | (_, VN_UVar({uvar_val = {contents = Set v}})) ->
       let po = reinsert (Ptr.V_ptr p2) po in
       unif_vptr po p1 p2
    | (VN_UVar(v1)   , VN_UVar(v2)   )
        when v1.uvar_key = v2.uvar_key -> assert false
    | (VN_UVar(v1)   , _             ) ->
       let (p, po) = canonical_valu p2 po in
       if uvar_occurs v1 p then raise NoUnif;
       uvar_set v1 p;
       union (Ptr.V_ptr p1) (Ptr.V_ptr p2) po
    | (_             , VN_UVar(v2)   ) ->
       let (p, po) = canonical_valu p1 po in
       if uvar_occurs v2 p then raise NoUnif;
       uvar_set v2 p;
       union (Ptr.V_ptr p2) (Ptr.V_ptr p1) po
    | _ ->
    match (n1, n2) with
    | (VN_LAbs(b1)   , VN_LAbs(b2)   ) ->
       unif_cl po V b1 b2
    | (VN_Cons(c1,p1), VN_Cons(c2,p2)) ->
       if c1.elt <> c2.elt then raise NoUnif;
       unif_vptr po p1 p2
    | (VN_Reco(m1)   , VN_Reco(m2)   ) ->
       if A.length m1 <> A.length m2 then raise NoUnif;
       A.fold2 unif_vptr po m1 m2
    | (VN_Scis       , VN_Scis       ) -> po
    | (VN_VWit(w1)   , VN_VWit(w2)   ) ->
       if !(w1.valu) == !(w2.valu) then po
       else if !(w1.vars) = [] && !(w2.vars) = [] then raise NoUnif
       else
         (let (f1,a1,b1) = !(w1.valu) in
          let (f2,a2,b2) = !(w2.valu) in
          let po = unif_bndr po V f1 f2 in
          let po = unif_expr po a1 a2 in
          unif_expr po b1 b2)
    | (VN_UWit(w1)   , VN_UWit(w2)   ) ->
       if !(w1.valu) == !(w2.valu) then po
       else if !(w1.vars) = [] && !(w2.vars) = [] then raise NoUnif
       else
         (let (_,t1,b1) = !(w1.valu) in
          let (_,t2,b2) = !(w2.valu) in
          let po = unif_expr po t1 t2 in
          unif_bndr po V b1 b2)
    | (VN_EWit(w1)   , VN_EWit(w2)   ) ->
       if !(w1.valu) == !(w2.valu) then po
       else if !(w1.vars) = [] && !(w2.vars) = [] then raise NoUnif
       else
         (let (_,t1,b1) = !(w1.valu) in
          let (_,t2,b2) = !(w2.valu) in
          let po = unif_expr po t1 t2 in
          unif_bndr po V b1 b2)
    | (VN_ITag(n1)   , VN_ITag(n2)   ) ->
       if n1 = n2 then po else raise NoUnif
    | (VN_HApp(e1)   , VN_HApp(e2)   ) ->
       unif_ho_appl po e1 e2
    | (VN_Goal(v1)   , VN_Goal(v2)   ) ->
       unif_expr po v1 v2
    | (_             , _             ) ->
       raise NoUnif
  end

and unif_t_nodes : pool -> TPtr.t -> t_node -> TPtr.t -> t_node -> pool =
  fun po p1 n1 p2 n2 -> if n1 == n2 then po else begin
    match (n1, n2) with
    | (TN_UVar({uvar_val = {contents = Set v}}), _) ->
       let po = reinsert (Ptr.T_ptr p1) po in
       unif_tptr po p1 p2
    | (_, TN_UVar({uvar_val = {contents = Set v}})) ->
       let po = reinsert (Ptr.T_ptr p2) po in
       unif_tptr po p1 p2
    | (TN_UVar(v1)   , TN_UVar(v2)   )
            when v1.uvar_key = v2.uvar_key -> assert false
    | (TN_UVar(v1)     , _               ) ->
       let (p, po) = canonical_term p2 po in
       if uvar_occurs v1 p then raise NoUnif;
       uvar_set v1 p;
       union (Ptr.T_ptr p1) (Ptr.T_ptr p2) po
    | (_               , TN_UVar(v2)     ) ->
       let (p, po) = canonical_term p1 po in
       if uvar_occurs v2 p then raise NoUnif;
       uvar_set v2 p;
       union (Ptr.T_ptr p2) (Ptr.T_ptr p1) po
    | _ ->
    match (n1, n2) with
    | (TN_Valu(p1)     , TN_Valu(p2)     ) ->
       unif_vptr po p1 p2
    | (TN_Appl(p11,p12), TN_Appl(p21,p22)) ->
       let po = unif_ptr po p11 p21 in
       unif_ptr po p12 p22
    | (TN_MAbs(b1)     , TN_MAbs(b2)     ) ->
       unif_cl po S b1 b2
    | (TN_Name(s1,p1)  , TN_Name(s2,p2)  ) ->
       let po = unif_expr po s1 s2 in
       unif_ptr po p1 p2
    | (TN_Proj(p1,l1)  , TN_Proj(p2,l2)  ) ->
       if l1.elt <> l2.elt then raise NoUnif;
       unif_vptr po p1 p2
    | (TN_Case(p1,m1)  , TN_Case(p2,m2)  ) ->
       if A.length m1 <> A.length m2 then raise NoUnif;
       let po = unif_vptr po p1 p2 in
       A.fold2 (fun po -> unif_cl po V) po m1 m2
    | (TN_FixY(b1)     , TN_FixY(b2     )) ->
       unif_cl po T b1 b2
    | (TN_Prnt(s1)     , TN_Prnt(s2)     ) ->
       if s1 <> s2 then raise NoUnif; po
    | (TN_UWit(w1)     , TN_UWit(w2)     ) ->
       if !(w1.valu) == !(w2.valu) then po
       else if !(w1.vars) = [] && !(w2.vars) = [] then raise NoUnif
       else
         (let (_,t1,b1) = !(w1.valu) in
          let (_,t2,b2) = !(w2.valu) in
          let po = unif_expr po t1 t2 in
          unif_bndr po T b1 b2)
    | (TN_EWit(w1)     , TN_EWit(w2)     ) ->
       if !(w1.valu) == !(w2.valu) then po
       else if !(w1.vars) = [] && !(w2.vars) = [] then raise NoUnif
       else
         (let (_,t1,b1) = !(w1.valu) in
          let (_,t2,b2) = !(w2.valu) in
          let po = unif_expr po t1 t2 in
          unif_bndr po T b1 b2)
    | (TN_ITag(n1)     , TN_ITag(n2)     ) ->
       if n1 <> n2 then raise NoUnif; po
    | (TN_HApp(e1)     , TN_HApp(e2)     ) ->
       unif_ho_appl po e1 e2
    | (TN_Goal(t1)     , TN_Goal(t2)     ) ->
       unif_expr po t1 t2
    | (_               , _               ) ->
       raise NoUnif
  end

and eq_val : pool ref -> valu -> valu -> bool = fun pool v1 v2 ->
  if v1.elt == v2.elt then true else
    begin
      let po = !pool in
      log2 "eq_val: inserting %a = %a in context\n%a" Print.ex v1
           Print.ex v2 (print_pool "        ") po;
      let (p1, po) = add_valu true po v1 in
      let (p2, po) = add_valu true po v2 in
      log2 "eq_val: insertion at %a and %a" VPtr.print p1 VPtr.print p2;
      log2 "eq_val: obtained context:\n%a" (print_pool "        ") po;
      try pool := (UTimed.apply (unif_vptr po p1) p2); true
      with NoUnif -> false
    end

and eq_trm : pool ref -> term -> term -> bool = fun pool t1 t2 ->
  if t1.elt == t2.elt then true else
    begin
      let po = !pool in
      log2 "eq_trm: inserting %a = %a in context\n%a" Print.ex t1
          Print.ex t2 (print_pool "        ") po;
      let (p1, po) = add_term true true po t1 in
      let (p2, po) = add_term true true po t2 in
      log2 "eq_trm: insertion at %a and %a" Ptr.print p1 Ptr.print p2;
      log2 "eq_trm: obtained context:\n%a" (print_pool "        ") po;
      try pool := (UTimed.apply (unif_ptr po p1) p2); true
      with NoUnif -> false
    end

and oracle pool = {
    eq_val = (fun v1 v2 ->
      Chrono.add_time equiv_chrono (eq_val pool v1) v2);
    eq_trm = (fun v1 v2 ->
      Chrono.add_time equiv_chrono (eq_trm pool v1) v2)
  }


(* Equational context type. *)
type eq_ctxt =
  { pool : pool }

let empty_ctxt : eq_ctxt =
  { pool = empty_pool }

type equiv   = term * term
type inequiv = term * term

(* Adds an equivalence to a context, producing a bigger context. The
   exception [Contradiction] is raised when expected. *)
let add_equiv : equiv -> eq_ctxt -> eq_ctxt = fun (t,u) {pool} ->
  log2 "add_equiv: inserting %a = %a in context\n%a" Print.ex t
    Print.ex u (print_pool "        ") pool;
  if eq_expr t u then
    begin
      log2 "add_equiv: trivial proof";
      {pool}
    end
  else
  let (pt, pool) = add_term true true pool t in
  let (pu, pool) = add_term true true pool u in
  log2 "add_equiv: insertion at %a and %a" Ptr.print pt Ptr.print pu;
  log2 "add_equiv: obtained context (1):\n%a" (print_pool "        ") pool;
  let pool = union pt pu pool in
  log2 "add_equiv: obtained context (2):\n%a" (print_pool "        ") pool;
  {pool}

let add_vptr_nobox : VPtr.t -> pool -> pool = fun vp po ->
  let (vp, po) = find (Ptr.V_ptr vp) po in
  match vp with
  | Ptr.T_ptr(_) -> assert false
  | Ptr.V_ptr(vp) ->
     if not (get_bs vp po) then
       begin
         let po = set_bs vp po in
         let nps = parents (Ptr.V_ptr vp) po in
         MapKey.fold (fun k l po -> PtrSet.fold reinsert l po) nps po
       end
     else po

let add_nobox : valu -> pool -> pool = fun v po ->
  log2 "add_nobox: inserting %a not box in context\n%a" Print.ex v
    (print_pool "        ") po;
  let (vp, po) = add_valu true po v in
  add_vptr_nobox vp po

(* Adds an inequivalence to a context, producing a bigger context. The
   exception [Contradiction] is raised when expected. *)
let add_inequiv : inequiv -> eq_ctxt -> eq_ctxt = fun (t,u) {pool} ->
  log2 "add_inequiv: inserting %a ≠ %a in context\n%a" Print.ex t
    Print.ex u (print_pool "        ") pool;
  if eq_expr t u then
    begin
      log2 "immediate contradiction";
      bottom ()
    end;
  let (pt, pool) = add_term true true pool t in
  let (pu, pool) = add_term true true pool u in
  log2 "add_inequiv: insertion at %a and %a" Ptr.print pt Ptr.print pu;
  log2 "add_inequiv: obtained context:\n%a" (print_pool "        ") pool;
  try
    ignore (UTimed.apply (unif_ptr pool pt) pu);
    log2 "add_inequiv: contradiction found";
    bottom ()
  with NoUnif -> {pool} (* TODO #3 store clauses *)

(* Main module interface. *)

(* epsilon for projection:
   proj_eps v l define a value w such v.l = w *)
let proj_eps : Bindlib.ctxt -> valu -> string -> valu * Bindlib.ctxt =
  fun names v l ->
    let eq x = equiv (valu None (vari None x))
                     true
                     (proj None (box v) (Pos.none l))
    in
    let bndr x = rest None unit_prod (eq x) in
    let t = Pos.none (Valu(Pos.none (Reco A.empty))) in
    ewit names V t (None, unbox (vbind (mk_free V) "x" bndr))

let find_proj : pool -> Bindlib.ctxt -> valu -> string
                -> valu * pool * Bindlib.ctxt =
  fun po names v l ->
    try
      let (vp, po) = add_valu true po v in
      let (vp, po) = find (Ptr.V_ptr vp) po in
      match vp with
      | Ptr.T_ptr(_) -> assert false (* Should never happen. *)
      | Ptr.V_ptr(vp) ->
         let n = find_v_node vp po in
         let (wp, w, po, names) =
           match n with
           | VN_Reco(m) ->
              let pt = A.find l m in
              (pt, Pos.none (VPtr pt), po, names)
           | _ ->
              let (w,names) = proj_eps names v l in
              let (wp,po) = add_valu true po w in
              let (pt,po) = add_term false true po
                                     (Pos.none (Proj(v,Pos.none l))) in
              let po = union (Ptr.V_ptr wp) pt po in
              (wp, w, po, names)
         in
         let po = if get_bs vp po then add_vptr_nobox wp po else po in
         (w, po, names)
  with e -> bug_msg "unexpected exception in find_proj: %s"
                    (Printexc.to_string e);
            assert false


(* NOTE: sum with one case should not fail, and be treated as projection *)
let find_sum : pool -> valu -> (string * valu * pool) option = fun po v ->
  try
    let (vp, po) = add_valu true po v in
    let (vp, po) = find (Ptr.V_ptr vp) po in
    match vp with
      | Ptr.T_ptr(_) -> raise Not_found
      | Ptr.V_ptr(vp) ->
         let n = find_v_node vp po in
         match n with
         | VN_Cons(c,pt) ->
            Some (c.elt, Pos.none (VPtr pt), po)
         | _ -> raise Not_found
  with Not_found -> None

exception Failed_to_prove of rel
let equiv_error : rel -> 'a =
  fun rel -> raise (Failed_to_prove rel)

(* Adds no box to the bool *)
let check_nobox : valu -> eq_ctxt -> bool * eq_ctxt = fun v {pool} ->
  log2 "inserting %a not box in context\n%a" Print.ex v
    (print_pool "        ") pool;
  let (vp, pool) = add_valu true pool v in
  let (vp, pool) = find (Ptr.V_ptr vp) pool in
  match vp with
  | Ptr.T_ptr(_)  -> (false, {pool})
  | Ptr.V_ptr(vp) -> (get_bs vp pool, { pool })

(* Test whether a term is equivalent to a value or not. *)
let is_value : term -> eq_ctxt -> bool * eq_ctxt = fun t {pool} ->
  log2 "inserting %a not box in context\n%a" Print.ex t
    (print_pool "        ") pool;
  let (pt, pool) = add_term true true pool t in
  log2 "insertion at %a" Ptr.print pt;
  log2 "obtained context:\n%a" (print_pool "        ") pool;
  let res = match pt with Ptr.V_ptr(_) -> true | Ptr.T_ptr(_) -> false in
  log2 "obtained context:\n%a" (print_pool "        ") pool;
  log "%a is%s a value" Print.ex t (if res then "" else " not");
  (res, {pool})

(* Test whether a term is equivalent to a value or not. *)
let to_value : term -> eq_ctxt -> valu option * eq_ctxt = fun t {pool} ->
  let (pt, pool) = add_term true true pool t in
  match pt with
  | Ptr.V_ptr(v) -> Some (Pos.none (VPtr v)), { pool }
  | Ptr.T_ptr(_) -> None, { pool }

let learn : eq_ctxt -> rel -> eq_ctxt = fun ctx rel ->
  log "learning %a" Print.rel rel;
  try
    let ctx =
      match rel with
      | Equiv(t,b,u) ->
         (if b then add_equiv else add_inequiv) (t,u) ctx
      | Posit _ -> assert false (* TODO #14 *)
      | NoBox(v) ->
         {pool = add_nobox v ctx.pool }
    in
    log "learned  %a" Print.rel rel; ctx
  with Contradiction ->
    log "contradiction in the context";
    raise Contradiction

let prove : eq_ctxt -> rel -> eq_ctxt = fun ctx rel ->
  log "proving  %a" Print.rel rel;
  try
    begin
      match rel with
      | Equiv(t,b,u) ->
         ignore ((if b then add_inequiv else add_equiv) (t,u) ctx);
      | Posit _ -> assert false (* TODO #14 *)
      | NoBox(v) ->
         let (b, ctx) = check_nobox v ctx in
         if b then raise Contradiction
    end;
    log "failed to prove %a" Print.rel rel;
    equiv_error rel
  with Contradiction ->
    log "proved   %a" Print.rel rel;
    ctx

let learn ctx rel     = Chrono.add_time equiv_chrono (learn ctx) rel
let prove ctx rel     = Chrono.add_time equiv_chrono (prove ctx) rel
let to_value t eqs    = Chrono.add_time equiv_chrono (to_value t) eqs
let is_value t eqs    = Chrono.add_time equiv_chrono (is_value t) eqs
let check_nobox v eqs = Chrono.add_time equiv_chrono (check_nobox v) eqs
let add_nobox v eqs   = Chrono.add_time equiv_chrono (add_nobox v) eqs
let find_proj eqs v   = Chrono.add_time equiv_chrono (find_proj eqs) v
let find_sum eqs v    = Chrono.add_time equiv_chrono (find_sum eqs) v
