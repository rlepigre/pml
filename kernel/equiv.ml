(** Equivalence decision procedure. During decision of equivalence, terms are
    stored in a graph (shared among all knonwn terms). Maximal sharing is
    attained by never inserting nodes that are already in the graph. Given
    such a graph (or pool), one will be able to read back the representative
    of a term by following the edges. *)

open Bindlib
open Sorts
open Pos
open Ast
open Output
open Compare

let equiv_chrono = Chrono.create "equiv"

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


(** Module for pointers on a term or a value node of the graph. *)
module Ptr =
  struct
    type t =
      | V_ptr of VPtr.t
      | T_ptr of TPtr.t

    let compare p1 p2 =
      match (p1, p2) with
      | (V_ptr _ , T_ptr _ ) -> -1
      | (T_ptr _ , V_ptr _ ) -> 1
      | (V_ptr p1, V_ptr p2) -> VPtr.compare p1 p2
      | (T_ptr p1, T_ptr p2) -> TPtr.compare p1 p2

    let print ch p =
      match p with
      | V_ptr p -> VPtr.print ch p
      | T_ptr p -> TPtr.print ch p
  end
module PtrMap = Map.Make(Ptr)
module PtrSet = Set.Make(Ptr)
module TPtrSet = Set.Make(TPtr)

type ('a, 'b) funptr = (v ex, (t ex, ('a, 'b) bndr) mbinder) mbinder

let compare_funptr : type a b.a sort -> (a, b) funptr -> (a, b) funptr -> int =
  fun s b1 b2 ->
    let c = ref 0 in
    let new_itag : type a. a sort -> a ex = fun s -> decr c; ITag(s,!c) in
    let a1 = mbinder_arity b1 in
    match compare a1 (mbinder_arity b2) with
    | 0 ->
       begin
         let vs = Array.init a1 (fun _ -> new_itag V) in
         let b1 = msubst b1 vs in
         let b2 = msubst b2 vs in
         let a1 = mbinder_arity b1 in
         match compare a1 (mbinder_arity b2) with
         | 0 ->
            let vs = Array.init a1 (fun _ -> new_itag T) in
            let b1 = msubst b1 vs in
            let b2 = msubst b2 vs in
            compare_bndr s b1 b2
         | c -> c
       end
    | c -> c

type anyfunptr = T : 'a sort * 'b sort * ('a, 'b) funptr -> anyfunptr
module Fun =
  struct
    type t = anyfunptr
    let compare (T (sa1,sr1,f1)) (T (sa2,sr2,f2)) =
      match compare_sort sa1 sa2 with
      | Eq ->
         begin
           match compare_sort sr1 sr2 with
           | Eq -> compare_funptr sa1 f1 f2
           | Lt -> -1 | Gt -> 1
         end
      | Lt -> -1 | Gt -> 1
  end
module FunMap = Map.Make(Fun)

type ('a,'b) closure = ('a, 'b) funptr * VPtr.t array * TPtr.t array

(** Type of a pointer map, used to keep track of equivalences. *)
type eq_map = Ptr.t PtrMap.t

(** Wrapper for higher-order application. *)
type _ ho_appl =
  | HO_Appl : 'a sort * ('a -> 'b) ex loc * 'a ex loc -> 'b ho_appl

let eq_ho_appl : type a. a ho_appl -> a ho_appl -> bool =
  fun a1 a2 ->
    let open Eq in
    let (HO_Appl(s1,f1,e1), HO_Appl(s2,f2,e2)) = (a1, a2) in
    match eq_sort s1 s2 with
    | Eq -> eq_expr f1 f2 && eq_expr e1 e2
    | NEq -> false

(** Type of a value node. *)
type v_node =
  | VN_LAbs of (v, t) closure
  | VN_Cons of A.key loc * VPtr.t
  | VN_Reco of VPtr.t A.t
  | VN_Scis
  | VN_VWit of int * ((v,t) bndr * p ex loc * p ex loc)
  | VN_UWit of int * (t ex loc * (v,p) bndr)
  | VN_EWit of int * (t ex loc * (v,p) bndr)
  | VN_HApp of v ho_appl
  | VN_UVar of v uvar
  | VN_ITag of int
  | VN_Goal of v ex loc
type v_map = (PtrSet.t * v_node) VPtrMap.t
type b_map = VPtrSet.t

(** Type of a term node. *)
type t_node =
  | TN_Valu of VPtr.t
  | TN_Appl of TPtr.t * TPtr.t
  | TN_MAbs of (s,t) closure
  | TN_Name of s ex loc * TPtr.t
  | TN_Proj of VPtr.t * A.key loc
  | TN_Case of VPtr.t * (v,t) closure A.t
  | TN_FixY of (v,t) closure * VPtr.t
  | TN_Prnt of string
  | TN_UWit of int * (t ex loc * (t,p) bndr)
  | TN_EWit of int * (t ex loc * (t,p) bndr)
  | TN_HApp of t ho_appl
  | TN_UVar of t uvar
  | TN_ITag of int
  | TN_Goal of t ex loc
type t_map = (PtrSet.t * t_node) TPtrMap.t

(** Printing function for value nodes. *)
let pcl : type a b. a sort -> out_channel -> (a, b) closure -> unit =
  fun s ch (funptr,vs,ts) ->
    let prnt = Printf.fprintf in
    let pex = Print.ex in
    let (vvars,b) = unmbind (mk_free V) funptr in
    let (tvars,b) = unmbind (mk_free T) b in
    let (var,t)   = unbind (mk_free s) (snd b) in
    let vvars = if vs = [||] then [||] else vvars in
    let tvars = if ts = [||] then [||] else tvars in
    let fn ch =
      Array.iter2 (fun v t ->
          prnt ch "%s<-%a" (name_of v) VPtr.print t) vvars vs
    in
    let gn ch =
      Array.iter2 (fun v t ->
          prnt ch "%s<-%a" (name_of v) TPtr.print t) tvars ts
    in
    prnt ch "%s.%a[%t][%t]" (name_of var) pex t fn gn


let print_v_node : out_channel -> v_node -> unit = fun ch n ->
  let prnt = Printf.fprintf in
  let pex = Print.ex in
  match n with
  | VN_LAbs(b)     -> prnt ch "VN_LAbs(%a)" (pcl V) b
  | VN_Cons(c,pv)  -> prnt ch "VN_Cons(%s,%a)" c.elt VPtr.print pv
  | VN_Reco(m)     -> let pelt ch (k, p) = prnt ch "%S=%a" k VPtr.print p in
                      prnt ch "VN_Reco(%a)" (Print.print_map pelt ":") m
  | VN_Scis        -> prnt ch "VN_Scis"
  | VN_VWit(_,w)   -> let (b,_,_) = w in
                      prnt ch "VN_VWit(ει%s)" (bndr_name b).elt
  | VN_UWit(_,w)   -> let (_,b) = w in
                      prnt ch "VN_UWit(ε∀%s)" (bndr_name b).elt
  | VN_EWit(_,w)   -> let (_,b) = w in
                      prnt ch "VN_EWit(ε∃%s)" (bndr_name b).elt
  | VN_HApp(e)     -> let HO_Appl(s,f,a) = e in
                      prnt ch "VN_HApp(%a)" pex (Pos.none (HApp(s,f,a)))
  | VN_UVar(v)     -> prnt ch "VN_UVar(%a)" pex (Pos.none (UVar(V,v)))
  | VN_ITag(n)     -> prnt ch "VN_ITag(%d)" n
  | VN_Goal(v)     -> prnt ch "VN_Goal(%a)" pex v
(** Printing function for term nodes. *)
let print_t_node : out_channel -> t_node -> unit = fun ch n ->
  let prnt = Printf.fprintf in
  let pex = Print.ex in
  match n with
  | TN_Valu(pv)    -> prnt ch "TN_Valu(%a)" VPtr.print pv
  | TN_Appl(pt,pu) -> prnt ch "TN_Appl(%a,%a)" TPtr.print pt TPtr.print pu
  | TN_MAbs(b)     -> prnt ch "TN_MAbs(%a)" (pcl S) b
  | TN_Name(s,pt)  -> prnt ch "TN_Name(%a,%a)" pex s TPtr.print pt
  | TN_Proj(pv,l)  -> prnt ch "TN_Proj(%a,%s)" VPtr.print pv  l.elt
  | TN_Case(pv,m)  -> let pelt ch (k, b) =
                        prnt ch "%S → %a" k (pcl V) b
                      in
                      let pmap = Print.print_map pelt "|" in
                      prnt ch "TN_Case(%a|%a)" VPtr.print pv pmap m
  | TN_FixY(b,pv)  -> prnt ch "TN_FixY(%a,%a)" (pcl V) b
                        VPtr.print pv
  | TN_Prnt(s)     -> prnt ch "TN_Prnt(%S)" s
  | TN_UWit(_,w)   -> let (_,b) = w in
                      prnt ch "TN_UWit(ε∀%s)" (bndr_name b).elt
  | TN_EWit(_,w)   -> let (_,b) = w in
                      prnt ch "TN_EWit(ε∃%s)" (bndr_name b).elt
  | TN_HApp(e)     -> let HO_Appl(s,f,a) = e in
                      let e = Pos.none (HApp(s,f,a)) in
                      prnt ch "TN_HApp(%a)" Print.ex e
  | TN_UVar(v)     -> prnt ch "TN_UVar(%a)" pex (Pos.none (UVar(T,v)))
  | TN_ITag(n)     -> prnt ch "TN_ITag(%d)" n
  | TN_Goal(t)     -> prnt ch "TN_Goal(%a)" pex t

(** Type of a pool. *)
type pool =
  { vs       : v_map
  ; ts       : t_map
  ; bs       : b_map
  ; next     : int
  ; eq_map   : eq_map
  ; vwit_map : ((v, t) bndr * p ex loc * p ex loc * v_node) list
  ; in_norm  : TPtrSet.t
  }

let funptrs : anyfunptr FunMap.t ref = ref FunMap.empty

let is_empty : pool -> bool =
  fun {vs; ts} -> VPtrMap.is_empty vs && TPtrMap.is_empty ts

(** Printing a pool (useful for debugging. *)
let print_pool : string -> out_channel -> pool -> unit = fun prefix ch po ->
  if is_empty po then Printf.fprintf ch "%sEMPTY" prefix else
  let {vs ; ts ; eq_map } = po in
  Printf.fprintf ch "%s#### Nodes ####\n" prefix;
  let fn k (ps, n) =
    let b = if VPtrSet.mem k po.bs then "*" else "" in
    Printf.fprintf ch "%s  %a%s\t→ %a\t← [%a]\n" prefix VPtr.print k b
      print_v_node n (print_list Ptr.print ",") (PtrSet.elements ps)
  in
  VPtrMap.iter fn vs;
  Printf.fprintf ch "%s---------------\n" prefix;
  let fn k (ps, n) =
    Printf.fprintf ch "%s  %a\t→ %a\t← [%a]\n" prefix TPtr.print k
      print_t_node n (print_list Ptr.print ",") (PtrSet.elements ps)
  in
  TPtrMap.iter fn ts;
  Printf.fprintf ch "%s#### Links ####\n" prefix;
  let fn p1 p2 =
    Printf.fprintf ch "%s  %a\t→ %a\n" prefix Ptr.print p1 Ptr.print p2
  in
  PtrMap.iter fn eq_map;
  Printf.fprintf ch "%s###############" prefix


(** Initial, empty pool. *)
let empty_pool : pool =
  { vs     = VPtrMap.empty
  ; ts     = TPtrMap.empty
  ; bs     = VPtrSet.empty
  ; next   = 0
  ; eq_map = PtrMap.empty
  ; vwit_map = []
  ; in_norm = TPtrSet.empty
  }

(** Node search. *)
let find_v_node : VPtr.t -> pool -> PtrSet.t * v_node = fun p po ->
  VPtrMap.find p po.vs

let find_t_node : TPtr.t -> pool -> PtrSet.t * t_node = fun p po ->
  TPtrMap.find p po.ts

(** Geting the children sons of a node. *)

let children_closure : type a b. (a, b) closure -> Ptr.t list =
  fun (_,vs,ts) ->
    let res = ref [] in
    Array.iter (fun vptr -> res := Ptr.V_ptr vptr :: !res) vs;
    Array.iter (fun tptr -> res := Ptr.T_ptr tptr :: !res) ts;
    !res

let children_v_node : v_node -> Ptr.t list = fun n ->
  match n with
  | VN_VWit _
  | VN_UWit _
  | VN_EWit _
  | VN_ITag _
  | VN_UVar _ (* TODO #50 check *)
  | VN_HApp _ (* TODO #50 check *)
  | VN_Goal _
  | VN_Scis       -> []
  | VN_LAbs b     -> children_closure b
  | VN_Cons(_,pv) -> [Ptr.V_ptr pv]
  | VN_Reco(m)    -> A.fold (fun _ p s -> Ptr.V_ptr p :: s) m []

let children_t_node : t_node -> Ptr.t list = fun n ->
  match n with
  | TN_Valu(pv)    -> [Ptr.V_ptr pv]
  | TN_Appl(pt,pu) -> [Ptr.T_ptr pt; Ptr.T_ptr pu]
  | TN_Name(_,pt)  -> [Ptr.T_ptr pt]
  | TN_Proj(pv,_)  -> [Ptr.V_ptr pv]
  | TN_Case(pv,cs) -> Ptr.V_ptr pv ::
                        A.fold (fun _ b acc -> children_closure b @ acc) cs []
  | TN_FixY(b,pv)  -> Ptr.V_ptr pv :: children_closure b
  | TN_UWit _
  | TN_EWit _
  | TN_Prnt _
  | TN_MAbs _
  | TN_Goal _
  | TN_HApp _  (* TODO #50 check *)
  | TN_UVar _  (* TODO #50 check *)
  | TN_ITag _    -> []

(** Adding a parent to a given node. *)
let add_parent_nodes : Ptr.t -> Ptr.t list-> pool -> pool = fun np ps po ->
  let fn po p =
    match p with
    | Ptr.V_ptr p ->
       let (ps, n) = find_v_node p po in
       { po with vs = VPtrMap.add p (PtrSet.add np ps, n) po.vs }
    | Ptr.T_ptr p ->
       let (ps, n) = find_t_node p po in
       { po with ts = TPtrMap.add p (PtrSet.add np ps, n) po.ts }
  in
  List.fold_left fn po ps

let add_parent_v_nodes : VPtr.t -> Ptr.t list -> pool -> pool =
  fun vp ps po -> add_parent_nodes (Ptr.V_ptr vp) ps po

let add_parent_t_nodes : TPtr.t -> Ptr.t list -> pool -> pool =
  fun tp ps po -> add_parent_nodes (Ptr.T_ptr tp) ps po

(** Obtain the parents of a pointed node. *)
let parents : Ptr.t -> pool -> PtrSet.t = fun p po ->
  match p with
  | Ptr.V_ptr vp -> fst (find_v_node vp po)
  | Ptr.T_ptr tp -> fst (find_t_node tp po)

let add_parents : Ptr.t -> PtrSet.t -> pool -> pool = fun p nps po ->
  match p with

  | Ptr.V_ptr vp ->
     let (ps, n) = find_v_node vp po in
     {po with vs = VPtrMap.add vp (PtrSet.union nps ps, n) po.vs}
  | Ptr.T_ptr tp ->
     let (ps, n) = find_t_node tp po in
     {po with ts = TPtrMap.add tp (PtrSet.union nps ps, n) po.ts}

(** Find operation (with path contraction). *)
let find : Ptr.t -> pool -> Ptr.t * pool = fun p po ->
  let rec follow p eq_map =
    try follow (PtrMap.find p eq_map) eq_map
    with Not_found -> p
  in
  let repr = follow p po.eq_map in
  let eq_map =
    if repr = p then po.eq_map
    else PtrMap.add p repr po.eq_map
  in
  (repr, {po with eq_map})

let find_valu : VPtr.t -> pool -> VPtr.t * pool = fun p po ->
  let (p, po) = find (Ptr.V_ptr p) po in
  match p with
  | Ptr.V_ptr p -> (p, po)
  | Ptr.T_ptr _ -> assert false

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

let eq_cl po s (f1,vs1,ts1 as cl1) (f2,vs2,ts2 as cl2) =
  let for_all2 f a1 a2 =
    try
      Array.iter2 (fun x y -> if not (f po x y) then raise Exit) a1 a2;
      true
    with Exit -> false
  in
  if f1 == f2 then
    for_all2 eq_vptr vs1 vs2 &&
    for_all2 eq_tptr ts1 ts2
  else
    (assert (compare_funptr s f1 f2 <> 0 ||
             (Printf.eprintf "%a\n%a\n%!" (pcl s) cl1 (pcl s) cl2; false));
     false)

(** Equality functions on nodes. *)
let eq_v_nodes : pool -> v_node -> v_node -> bool =
  fun po n1 n2 -> n1 == n2 ||
    let eq_expr e1 e2 = eq_expr ~strict:true e1 e2 in
    (* FIXME #40, use oracle for VN_LAbs *)
    (* FIXME #50 (note), share VN_VWit and alike *)
    match (n1, n2) with
    | (VN_LAbs(b1)   , VN_LAbs(b2)   ) -> eq_cl po V b1 b2
    | (VN_Cons(c1,p1), VN_Cons(c2,p2)) -> c1.elt = c2.elt && eq_vptr po p1 p2
    | (VN_Reco(m1)   , VN_Reco(m2)   ) -> A.equal (eq_vptr po) m1 m2
    | (VN_Scis       , VN_Scis       ) -> true
    | (VN_VWit(_,w1) , VN_VWit(_,w2) ) -> w1 == w2 ||
                                            (let (f1,a1,b1) = w1 in
                                             let (f2,a2,b2) = w2 in
                                             eq_bndr V f1 f2 && eq_expr a1 a2
                                             && eq_expr b1 b2)
    | (VN_UWit(_,w1) , VN_UWit(_,w2) ) -> w1 == w2 ||
                                            (let (t1,b1) = w1 in
                                             let (t2,b2) = w2 in
                                             eq_expr t1 t2 && eq_bndr V b1 b2)
    | (VN_EWit(_,w1) , VN_EWit(_,w2) ) -> w1 == w2 ||
                                            (let (t1,b1) = w1 in
                                             let (t2,b2) = w2 in
                                             eq_expr t1 t2 && eq_bndr V b1 b2)
    | (VN_ITag(n1)   , VN_ITag(n2)   ) -> n1 = n2
    | (VN_HApp(e1)   , VN_HApp(e2)   ) -> eq_ho_appl e1 e2
    | (VN_Goal(v1)   , VN_Goal(v2)   ) -> eq_expr v1 v2
    | (_             , _             ) -> false

let eq_t_nodes : pool -> t_node -> t_node -> bool =
  fun po n1 n2 -> n1 == n2 ||
    let eq_expr e1 e2 = eq_expr ~strict:true e1 e2 in
    (* FIXME #40, use oracle for TN_MAbs and alike *)
    (* FIXME #50 (note), share VN_VWit and alike *)
    match (n1, n2) with
    | (TN_Valu(p1)     , TN_Valu(p2)     ) -> eq_vptr po p1 p2
    | (TN_Appl(p11,p12), TN_Appl(p21,p22)) -> eq_tptr po p11 p21
                                              && eq_tptr po p12 p22
    | (TN_MAbs(b1)     , TN_MAbs(b2)     ) -> eq_cl po S b1 b2
    | (TN_Name(s1,p1)  , TN_Name(s2,p2)  ) -> eq_expr s1 s2
                                              && eq_tptr po p1 p2
    | (TN_Proj(p1,l1)  , TN_Proj(p2,l2)  ) -> eq_vptr po p1 p2
                                              && l1.elt = l2.elt
    | (TN_Case(p1,m1)  , TN_Case(p2,m2)  ) -> eq_vptr po p1 p2
                                              && A.equal (eq_cl po V) m1 m2
    | (TN_FixY(b1,p1)  , TN_FixY(b2,p2)  ) -> eq_cl po V b1 b2
                                              && eq_vptr po p1 p2
    | (TN_Prnt(s1)     , TN_Prnt(s2)     ) -> s1 = s2
    | (TN_UWit(_,w1)   , TN_UWit(_,w2)   ) -> w1 == w2 ||
                                                (let (t1,b1) = w1 in
                                                 let (t2,b2) = w2 in
                                                 eq_expr t1 t2 && eq_bndr T b1 b2)
    | (TN_EWit(_,w1)   , TN_EWit(_,w2)   ) -> w1 == w2 ||
                                                (let (t1,b1) = w1 in
                                                 let (t2,b2) = w2 in
                                                 eq_expr t1 t2 && eq_bndr T b1 b2)
    | (TN_ITag(n1)     , TN_ITag(n2)     ) -> n1 = n2
    | (TN_HApp(e1)     , TN_HApp(e2)     ) -> eq_ho_appl e1 e2
    | (TN_Goal(t1)     , TN_Goal(t2)     ) -> eq_expr t1 t2
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
exception FoundV of VPtr.t
let insert_v_node : v_node -> pool -> VPtr.t * pool = fun nn po ->
  let children = children_v_node nn in
  try
    match children with
    | [] ->
       let fn p (_,n) = if eq_v_nodes po n nn then raise (FoundV p) in
       VPtrMap.iter fn po.vs; raise Not_found
    | n::_ ->
       let fn n = match n with
         | Ptr.T_ptr _ -> ()
         | Ptr.V_ptr n ->
            if eq_v_nodes po (snd (find_v_node n po)) nn then raise (FoundV n)
       in
       PtrSet.iter fn (parents n po); raise Not_found
  with
  | FoundV(p) -> (p, po)
  | Not_found ->
      let ptr = VPtr.V po.next in
      let vs = VPtrMap.add ptr (PtrSet.empty, nn) po.vs in
      let next = po.next + 1 in
      let bs = if immediate_nobox nn then VPtrSet.add ptr po.bs else po.bs in
      let po = { po with vs ; bs; next } in
      let po = add_parent_v_nodes ptr children po in
      (ptr, po)

exception FoundT of TPtr.t
let insert_t_node : t_node -> pool -> TPtr.t * pool = fun nn po ->
  let children = children_t_node nn in
  try
    match children with
    | [] ->
       let fn p (_,n) = if eq_t_nodes po n nn then raise (FoundT p) in
       TPtrMap.iter fn po.ts; raise Not_found
    | n::_ ->
       let fn n = match n with
         | Ptr.V_ptr _ -> ()
         | Ptr.T_ptr n ->
            if eq_t_nodes po (snd (find_t_node n po)) nn then raise (FoundT n)
       in
       PtrSet.iter fn (parents n po); raise Not_found
  with
  | FoundT(p) -> (p, po)
  | Not_found ->
      let ptr = TPtr.T po.next in
      let ts = TPtrMap.add ptr (PtrSet.empty, nn) po.ts in
      let eq_map =
        match nn with
        | TN_Valu(pv) -> PtrMap.add (Ptr.T_ptr ptr) (Ptr.V_ptr pv) po.eq_map
        | _            -> po.eq_map
      in
      let next = po.next + 1 in
      let po = { po with eq_map; ts ; next } in
      let po = add_parent_t_nodes ptr children po in
      (ptr, po)

(** Insertion of actual terms and values to the pool. *)
let rec add_term : pool -> term -> TPtr.t * pool = fun po t ->
  let t = Norm.whnf t in
  match t.elt with
  | Valu(v)     -> let (pv, po) = add_valu po v in
                   insert_t_node (TN_Valu(pv)) po
  | Appl(t,u)   -> let (pt, po) = add_term po t in
                   let (pu, po) = add_term po u in
                   insert_t_node (TN_Appl(pt,pu)) po
  | MAbs(b)     -> let (cl, po) = add_closure po S T b in
                   insert_t_node (TN_MAbs(cl)) po
  | Name(s,t)   -> let (pt, po) = add_term po t in
                   insert_t_node (TN_Name(s,pt)) po
  | Proj(v,l)   -> let (pv, po) = add_valu po v in
                   insert_t_node (TN_Proj(pv,l)) po
  | Case(v,m)   -> let (pv, po) = add_valu po v in
                   let (m,  po) = A.fold_map
                                    (fun _ (_,x) pos -> add_closure po V T x)
                                    m po
                   in
                   insert_t_node (TN_Case(pv,m)) po
  | FixY(b,v)   -> let (pv, po) = add_valu po v in
                   let (b,  po) = add_closure po V T b in
                   insert_t_node (TN_FixY(b,pv)) po
  | Prnt(s)     -> insert_t_node (TN_Prnt(s)) po
  | Coer(_,t,_) -> add_term po t
  | Such(_,_,r) -> add_term po (bseq_dummy r.binder)
  | UWit(i,_,w) -> insert_t_node (TN_UWit(i,w)) po
  | EWit(i,_,w) -> insert_t_node (TN_EWit(i,w)) po
  | HApp(s,f,a) -> insert_t_node (TN_HApp(HO_Appl(s,f,a))) po
  | HDef(_,d)   -> add_term po d.expr_def
  | UVar(_,v)   -> insert_t_node (TN_UVar(v)) po
  | ITag(_,n)   -> insert_t_node (TN_ITag(n)) po
  | Goal(_)     -> insert_t_node (TN_Goal(t)) po
  | TPtr(pt)    -> (pt, po)
  | Vari(_)     -> invalid_arg "free variable in the pool"
  | Dumm        -> invalid_arg "dummy terms forbidden in the pool"

and     add_valu : pool -> valu -> VPtr.t * pool = fun po v ->
  let v = Norm.whnf v in
  match v.elt with
  | LAbs(_,b)   -> let (b, po) = add_closure po V T b in
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
  | VDef(d)     -> add_valu po (Erase.to_valu d.value_eval)
  | Coer(_,v,_) -> add_valu po v
  | Such(_,_,r) -> add_valu po (bseq_dummy r.binder)
  | VWit(i,w)   -> insert_v_node (VN_VWit(i,w)) po
  | UWit(i,_,w) -> insert_v_node (VN_UWit(i,w)) po
  | EWit(i,_,w) -> insert_v_node (VN_EWit(i,w)) po
  | HApp(s,f,a) -> insert_v_node (VN_HApp(HO_Appl(s,f,a))) po
  | HDef(_,d)   -> add_valu po d.expr_def
  | UVar(_,v)   -> insert_v_node (VN_UVar(v)) po
  | ITag(_,n)   -> insert_v_node (VN_ITag(n)) po
  | Goal(_)     -> insert_v_node (VN_Goal(v)) po
  | VPtr(pv)    -> (pv, po)
  | Vari(_)     -> invalid_arg "free variable in the pool"
  | Dumm        -> invalid_arg "dummy terms forbidden in the pool"

and add_closure : type a b. pool -> a sort -> b sort ->
                       (a, b) bndr -> (a, b) closure * pool =
  fun po sa sr b ->
    let (funptr, vs, ts as cl) = Misc.make_closure sa b in
    let po = ref po in
    let vs = Array.map (fun v -> let (vptr,p) = add_valu !po v in
                                 po := p; vptr) vs
    in
    let ts = Array.map (fun t -> let (tptr,p) = add_term !po t in
                                 po := p; tptr) ts
    in
    let po = !po in
    let key = T(sa,sr,funptr) in
    (*print_pool "TEST" stderr po;*)
    try
      let T(sa',sr',funptr') = FunMap.find key !funptrs in
      match eq_sort sa sa', eq_sort sr sr' with
      | Eq.Eq, Eq.Eq -> ((funptr',vs,ts), po)
      | _ -> assert false
    with Not_found ->
      funptrs := FunMap.add key key !funptrs;
      ((funptr,vs,ts), po)

(** Creation of a [TPtr.t] from a [Ptr.t]. A value node is inserted in the
    pool in case of a [VPtr.t]. *)
let as_term : Ptr.t -> pool -> TPtr.t * pool = fun p po ->
  match p with
  | Ptr.T_ptr pt -> (pt, po)
  | Ptr.V_ptr pv -> insert_t_node (TN_Valu(pv)) po

(** Insertion of an application node with arbitrary pointer kind. *)
let insert_appl : Ptr.t -> Ptr.t -> pool -> Ptr.t * pool = fun pt pu po ->
  let (pt, po) = as_term pt po in
  let (pu, po) = as_term pu po in
  let (p,  po) = insert_t_node (TN_Appl(pt,pu)) po in
  find (Ptr.T_ptr p) po

let subst_closure (funptr,vs,ts) =
  let vs = Array.map (fun v -> VPtr v) vs in
  let ts = Array.map (fun t -> TPtr t) ts in
  msubst (msubst funptr vs) ts

(** Normalisation function. *)
let rec normalise : TPtr.t -> pool -> Ptr.t * pool =
  fun p po ->
    let in_norm = po.in_norm in
    if TPtrSet.mem p in_norm then find (Ptr.T_ptr p) po else
    let po = { po with in_norm = TPtrSet.add p in_norm } in
    let (p, po) =
       match snd (TPtrMap.find p po.ts) with
       | TN_Valu(pv)    -> (Ptr.V_ptr pv, po)
       | TN_Appl(pt,pu) ->
          begin
            log2 "normalise in TN_Appl: %a %a" TPtr.print pt TPtr.print pu;
            let (pt, po) = normalise pt po in
            let (pu, po) = normalise pu po in
             (* argument must be really normalised, even is update is true *)
            let (tp, po) = insert_appl pt pu po in
            let po = union (Ptr.T_ptr p)  tp po in
            log2 "normalised in TN_Appl: %a %a => %a"
                    Ptr.print pt Ptr.print pu  Ptr.print tp;
            match (pt, pu) with
            | (Ptr.V_ptr pf, Ptr.V_ptr pv) ->
               begin
                 match snd (VPtrMap.find pf po.vs), VPtrSet.mem pv po.bs with
                 | VN_LAbs(b), true ->
                    begin
                      let b = subst_closure b in
                      let t = bndr_subst b (VPtr pv) in
                      let (tp, po) = add_term po t in
                      let po = union (Ptr.T_ptr p) (Ptr.T_ptr tp) po in
                      normalise tp po
                    end
                 | _          ->
                    log2 "normalised insert(1) TN_Appl: %a" Ptr.print tp;
                    (tp, po)
               end
            | (_           , _           ) ->
               log2 "normalised insert(2) TN_Appl: %a" Ptr.print tp;
                (tp, po)
          end
       | TN_MAbs(b)     -> (Ptr.T_ptr p, po) (* FIXME #45 can do better. *)
       | TN_Name(s,pt)  -> (Ptr.T_ptr p, po) (* FIXME #45 can do better. *)
       | TN_Proj(pv,l)  ->
          begin
            let (pv, po) = find_valu pv po in
            match snd (VPtrMap.find pv po.vs) with
            | VN_Reco(m) ->
               begin
                 try
                   let (tp, po) = find (Ptr.V_ptr (A.find l.elt m)) po in
                   let po = union (Ptr.T_ptr p) tp po in
                   (tp, po)
                 with Not_found -> (Ptr.T_ptr p, po)
               end
            | _          -> (Ptr.T_ptr p, po)
          end
       | TN_Case(pv,m)  ->
          begin
            let (pv, po) = find_valu pv po in
            log2 "normalisation in TN_Case: %a" VPtr.print pv;
            match snd (VPtrMap.find pv po.vs) with
            | VN_Cons(c,pv) ->
               begin
                 try
                   let b = subst_closure (A.find c.elt m) in
                   let t = bndr_subst b (VPtr pv) in
                   let (tp, po) = add_term po t in
                   let po = union (Ptr.T_ptr p) (Ptr.T_ptr tp) po in
                   normalise tp po
                 with
                   Not_found -> (Ptr.T_ptr p, po)
               end
            | _            -> (Ptr.T_ptr p, po)
          end
       | TN_FixY(f,pv)  ->
          begin
            log2 "normalisation in TN_FixY: %a" VPtr.print pv;
            let f = subst_closure f in
            let b = bndr_from_fun "x" (fun x -> FixY(f, Pos.none x)) in
            let t = bndr_subst f (LAbs(None, b)) in
            let (pt, po) = add_term po t in
            let (pu, po) = insert_t_node (TN_Valu(pv)) po in
            let (pap, po) = insert_t_node (TN_Appl(pt, pu)) po in
            let po = union (Ptr.T_ptr p) (Ptr.T_ptr pap) po in
            let (res, po) = normalise pap po in
            (res, po)
          end
       | TN_Prnt(_)     -> (Ptr.T_ptr p, po)
       | TN_UWit(_)     -> (Ptr.T_ptr p, po)
       | TN_EWit(_)     -> (Ptr.T_ptr p, po)
       | TN_HApp(_)     -> (Ptr.T_ptr p, po)
       | TN_Goal(_)     -> (Ptr.T_ptr p, po)
       | TN_UVar(v)     ->
          begin
            match !(v.uvar_val) with
            | None   -> (Ptr.T_ptr p, po)
            | Some t -> let (tp, po) = add_term po t in
                        let po = union (Ptr.T_ptr p) (Ptr.T_ptr tp) po in
                        normalise tp po
          end
       | TN_ITag(n)      -> (Ptr.T_ptr p, po)
    in
    find p { po with in_norm }

and check_eq : Ptr.t -> Ptr.t -> pool -> pool = fun p1 p2 po ->
  let (p1, po) = find p1 po in
  let (p2, po) = find p2 po in
  if p1 = p2 then po else
    match (p1, p2) with
    | Ptr.V_ptr vp1, Ptr.V_ptr vp2 ->
       let (pp1, n1) = find_v_node vp1 po in
       let (pp2, n2) = find_v_node vp2 po in
       if eq_v_nodes po n1 n2 then union p1 p2 po else po
    | Ptr.T_ptr tp1, Ptr.T_ptr tp2 ->
       let (pp1, n1) = find_t_node tp1 po in
       let (pp2, n2) = find_t_node tp2 po in
       if eq_t_nodes po n1 n2 then join p1 p2 po else po
    | _ -> po

and check_parents_eq pp1 pp2 po =
  PtrSet.fold (fun p1 po ->
      PtrSet.fold (fun p2 po ->
          check_eq p1 p2 po) pp2 po)
              pp1 po

and reinsert : Ptr.t -> pool -> pool = fun p po ->
  match p with
  | Ptr.T_ptr tp ->
     let (pp1, n1) = find_t_node tp po in
     begin
       match n1 with
       | TN_Valu(_) | TN_UVar(_) ->
          PtrSet.fold reinsert pp1 po
       | _ ->
          log2 "normalisation of parent %a" TPtr.print tp;
          let (p', po) = normalise tp po in
          log2 "normalised parent %a at %a" TPtr.print tp Ptr.print p';
          po
     end
  | _           -> po

and join_nobox : Ptr.t -> Ptr.t -> pool -> pool = fun p1 p2 po ->
  match p1, p2 with
  | Ptr.V_ptr pv1, Ptr.V_ptr pv2 ->
     if VPtrSet.mem pv1 po.bs && not (VPtrSet.mem pv2 po.bs) then
       { po with bs = VPtrSet.add pv2 po.bs }
     else
       po
  | _ -> po

(** Union operation. *)
and join : Ptr.t -> Ptr.t -> pool -> pool = fun p1 p2 po ->
  let nps = parents p1 po in
  let pp2 = parents p2 po in
  let po = { po with eq_map = PtrMap.add p1 p2 po.eq_map } in
  let po = join_nobox p1 p2 po in
  let po = add_parents p2 nps po in
  let po = check_parents_eq nps pp2 po in
  PtrSet.fold reinsert nps po

(* when the join can be arbitrary, better to point to
   the oldest pointer (likely to given less occur-check failure*)
and age_join : Ptr.t -> Ptr.t -> pool -> pool = fun p1 p2 po ->
  if p2 > p1 then join p1 p2 po else join p2 p1 po

and union : Ptr.t -> Ptr.t -> pool -> pool = fun p1 p2 po ->
  let (p1, po) = find p1 po in
  let (p2, po) = find p2 po in
  if p1 = p2 then po else
    match (p1, p2) with
    | (Ptr.T_ptr _  , Ptr.V_ptr _  ) -> join p1 p2 po
    | (Ptr.V_ptr _  , Ptr.T_ptr _  ) -> join p2 p1 po
    | (Ptr.T_ptr _  , Ptr.T_ptr _  ) -> age_join p1 p2 po
    | (Ptr.V_ptr vp1, Ptr.V_ptr vp2) ->
       begin
         let (_,n1) = VPtrMap.find vp1 po.vs in
         let (_,n2) = VPtrMap.find vp2 po.vs in
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
            union (Ptr.V_ptr vp1) (Ptr.V_ptr vp2) po
         (* Records. *)
         | (VN_Reco(m1)    , VN_Reco(m2)    ) ->
            let po = ref (age_join p1 p2 po) in
            let test vp1 vp2 =
              po := union (Ptr.V_ptr vp1) (Ptr.V_ptr vp2) !po; true
            in
            if not (A.equal test m1 m2) then bottom ();
            !po
         (* Prefer real values as equivalence class representatives. *)
         | (VN_LAbs(_)     , _              )
           | (VN_Reco(_)     , _              )
           | (VN_Cons(_,_)   , _              ) -> join p2 p1 po
         | (_              , VN_LAbs(_)     )
           | (_              , VN_Reco(_)     )
           | (_              , VN_Cons(_,_)   ) -> join p1 p2 po
         (* age_join otherwise. *)
         | (_              , _              ) ->
            age_join p2 p1 po
       end

(** Obtain the canonical term / value pointed by a pointer. *)
let rec canonical_term : TPtr.t -> pool -> term * pool = fun p po ->
  let (p, po) = find (Ptr.T_ptr p) po in
  match p with
  | Ptr.T_ptr(p) ->
      begin
        match snd (TPtrMap.find p po.ts) with
        | TN_Valu(pv)    -> let (v, po) = canonical_valu pv po in
                            (Pos.none (Valu(v)), po)
        | TN_Appl(pt,pu) -> let (t, po) = canonical_term pt po in
                            let (u, po) = canonical_term pu po in
                            (Pos.none (Appl(t,u)), po)
        | TN_MAbs(b)     -> let (b, po) = canonical_closure b po in
                            (Pos.none (MAbs(b)), po)
        | TN_Name(s,pt)  -> let (t, po) = canonical_term pt po in
                            (Pos.none (Name(s,t)), po)
        | TN_Proj(pv,l)  -> let (v, po) = canonical_valu pv po in
                            (Pos.none (Proj(v,l)), po)
        | TN_Case(pv,m)  -> let (v, po) = canonical_valu pv po in
                            let (m, po) = A.fold_map (fun _ b po ->
                                              let (p, po) = canonical_closure b po in
                                              ((None, p), po)) m po
                            in
                            (Pos.none (Case(v, m)), po)
        | TN_FixY(b,pv)  -> let (v, po) = canonical_valu pv po in
                            let (b, po) = canonical_closure b po in
                            (Pos.none (FixY(b,v)), po)
        | TN_Prnt(s)     -> (Pos.none (Prnt(s)), po)
        | TN_UWit(i,w)   -> (Pos.none (UWit(i,T,w)), po)
        | TN_EWit(i,w)   -> (Pos.none (EWit(i,T,w)), po)
        | TN_HApp(e)     -> let HO_Appl(s,f,a) = e in
                            (Pos.none (HApp(s,f,a)), po)
        | TN_UVar(v)     -> begin
                              match !(v.uvar_val) with
                              | None   -> (Pos.none (UVar(T,v)), po)
                              | Some t ->
                                  let (p, po) = add_term po t in
                                  canonical_term p po
                            end
        | TN_ITag(n)     -> (Pos.none (ITag(T,n)), po)
        | TN_Goal(t)     -> (t, po)
      end
  | Ptr.V_ptr(p) ->
      let (v, po) = canonical_valu p po in
      (Pos.none (Valu(v)), po)

and     canonical_valu : VPtr.t -> pool -> valu * pool = fun p po ->
  let (p, po) = find (Ptr.V_ptr p) po in
  match p with
  | Ptr.T_ptr(p) -> assert false (* Should never happen. *)
  | Ptr.V_ptr(p) ->
      begin
        match snd (VPtrMap.find p po.vs) with
        | VN_LAbs(b)     -> let (b, po) = canonical_closure b po in
                            (Pos.none (LAbs(None, b)), po)
        | VN_Cons(c,pv)  -> let (v, po) = canonical_valu pv po in
                            (Pos.none (Cons(c,v)), po)
        | VN_Reco(m)     -> let fn l pv (m, po) =
                              let (v, po) = canonical_valu pv po in
                              (A.add l (None,v) m, po)
                            in
                            let (m, po) = A.fold fn m (A.empty, po) in
                            (Pos.none (Reco(m)), po)
        | VN_Scis        -> (Pos.none Scis, po)
        | VN_VWit(i,w)   -> (Pos.none (VWit(i,w)), po)
        | VN_UWit(i,w)   -> (Pos.none (UWit(i,V,w)), po)
        | VN_EWit(i,w)   -> (Pos.none (EWit(i,V,w)), po)
        | VN_HApp(e)     -> let HO_Appl(s,f,a) = e in
                            (Pos.none (HApp(s,f,a)), po)
        | VN_UVar(v)     -> begin
                              match !(v.uvar_val) with
                              | None   -> (Pos.none (UVar(V,v)), po)
                              | Some w ->
                                  let (p, po) = add_valu po w in
                                  canonical_valu p po
                            end
        | VN_ITag(n)     -> (Pos.none (ITag(V,n)), po)
        | VN_Goal(v)     -> (v, po)

      end

and canonical_closure : type a b.(a,b) closure -> pool -> (a,b) bndr * pool =
  fun (funptr,vs,ts) po ->
    let po = ref po in
    let vs = Array.map (fun p -> let (p, po') = canonical_valu p !po in
                                 po := po'; p.elt) vs
    in
    let ts = Array.map (fun p -> let (p, po') = canonical_term p !po in
                                 po := po'; p.elt) ts
    in
    (msubst (msubst funptr vs) ts, !po)

let canonical : Ptr.t -> pool -> term * pool = fun p po ->
  match p with
  | Ptr.T_ptr p -> canonical_term p po
  | Ptr.V_ptr p -> let (v, po) = canonical_valu p po in
                   (Pos.none (Valu v), po)

exception NoUnif

let rec unif_cl : type a b.pool -> a sort -> (a,b) closure -> (a,b) closure -> pool =
  fun po s (f1,vs1,ts1) (f2,vs2,ts2 ) ->
    let po = ref po in
    if f1 == f2 then
      begin
        Array.iter2 (fun v1 v2 -> po := unif_vptr !po v1 v2) vs1 vs2;
        Array.iter2 (fun t1 t2 -> po := unif_tptr !po t1 t2) ts1 ts2;
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
  match p1, p2 with
  | (Ptr.V_ptr p1, Ptr.V_ptr p2) ->
     let (_, v1) = find_v_node p1 po in
     let (_, v2) = find_v_node p2 po in
     unif_v_nodes po p1 v1 p2 v2
  | (Ptr.T_ptr p1, Ptr.T_ptr p2) ->
     let (_, v1) = find_t_node p1 po in
     let (_, v2) = find_t_node p2 po in
     unif_t_nodes po p1 v1 p2 v2
  | _ -> raise NoUnif (* FIXME: unif *)

(** Equality functions on nodes. *)
and unif_v_nodes : pool -> VPtr.t -> v_node -> VPtr.t -> v_node -> pool =
  fun po p1 n1 p2 n2 -> if n1 == n2 then po else
    let eq_expr po e1 e2 =
      let po = ref po in
      if eq_expr ~oracle:(oracle po) ~strict:false e1 e2 then !po
      else raise NoUnif
    in
    let eq_bndr po s e1 e2 =
      let po = ref po in
      if eq_bndr ~oracle:(oracle po) ~strict:false s e1 e2 then !po
      else raise NoUnif
    in
    (* FIXME #40, use oracle for VN_LAbs *)
    (* FIXME #50 (note), share VN_VWit and alike *)
    match (n1, n2) with
    | (VN_LAbs(b1)   , VN_LAbs(b2)   ) -> unif_cl po V b1 b2
    | (VN_Cons(c1,p1), VN_Cons(c2,p2)) -> if c1.elt <> c2.elt then raise NoUnif;
                                          unif_vptr po p1 p2
    | (VN_Reco(m1)   , VN_Reco(m2)   ) -> A.fold2 unif_vptr po m1 m2
    | (VN_Scis       , VN_Scis       ) -> po
    | (VN_VWit(_,w1) , VN_VWit(_,w2) ) -> if w1 == w2 then po else
                                            (let (f1,a1,b1) = w1 in
                                             let (f2,a2,b2) = w2 in
                                             let po = eq_bndr po V f1 f2 in
                                             let po = eq_expr po a1 a2 in
                                             eq_expr po b1 b2)
    | (VN_UWit(_,w1) , VN_UWit(_,w2) ) -> if w1 == w2 then po else
                                            (let (t1,b1) = w1 in
                                             let (t2,b2) = w2 in
                                             let po = eq_expr po t1 t2 in
                                             eq_bndr po V b1 b2)
    | (VN_EWit(_,w1) , VN_EWit(_,w2) ) -> if w1 == w2 then po else
                                            (let (t1,b1) = w1 in
                                             let (t2,b2) = w2 in
                                             let po = eq_expr po t1 t2 in
                                             eq_bndr po V b1 b2)
    | (VN_ITag(n1)   , VN_ITag(n2)   ) -> if n1 = n2 then po else raise NoUnif
    | (VN_HApp(e1)   , VN_HApp(e2)   ) -> if eq_ho_appl e1 e2 then po else raise NoUnif
    | (VN_Goal(v1)   , VN_Goal(v2)   ) -> eq_expr po v1 v2
    | (VN_UVar(v1)   , _             ) -> let (p, po) = canonical_valu p2 po in
                                          uvar_set v1 p;
                                          union (Ptr.V_ptr p1) (Ptr.V_ptr p2) po
    | (_             , VN_UVar(v2)   ) -> let (p, po) = canonical_valu p1 po in
                                          uvar_set v2 p;
                                          union (Ptr.V_ptr p1) (Ptr.V_ptr p2) po
    | (_             , _             ) -> raise NoUnif

and unif_t_nodes : pool -> TPtr.t -> t_node -> TPtr.t -> t_node -> pool =
  fun po p1 n1 p2 n2 -> if n1 == n2 then po else
    let eq_expr po e1 e2 =
      let po = ref po in
      if eq_expr ~oracle:(oracle po) ~strict:false e1 e2 then !po
      else raise NoUnif
    in
    let eq_bndr po s e1 e2 =
      let po = ref po in
      if eq_bndr ~oracle:(oracle po) ~strict:false s e1 e2 then !po
      else raise NoUnif
    in
    (* FIXME #40, use oracle for TN_MAbs and alike *)
    (* FIXME #50 (note), share VN_VWit and alike *)
    match (n1, n2) with
    | (TN_Valu(p1)     , TN_Valu(p2)     ) -> unif_vptr po p1 p2
    | (TN_Appl(p11,p12), TN_Appl(p21,p22)) -> let po = unif_tptr po p11 p21 in
                                              unif_tptr po p12 p22
    | (TN_MAbs(b1)     , TN_MAbs(b2)     ) -> unif_cl po S b1 b2
    | (TN_Name(s1,p1)  , TN_Name(s2,p2)  ) -> let po = eq_expr po s1 s2 in
                                              unif_tptr po p1 p2
    | (TN_Proj(p1,l1)  , TN_Proj(p2,l2)  ) -> if l1.elt <> l2.elt then raise NoUnif;
                                              unif_vptr po p1 p2
    | (TN_Case(p1,m1)  , TN_Case(p2,m2)  ) -> let po = unif_vptr po p1 p2 in
                                              A.fold2 (fun po -> unif_cl po V) po m1 m2
    | (TN_FixY(b1,p1)  , TN_FixY(b2,p2)  ) -> let po = unif_cl po V b1 b2 in
                                              unif_vptr po p1 p2
    | (TN_Prnt(s1)     , TN_Prnt(s2)     ) -> if s1 <> s2 then raise NoUnif; po
    | (TN_UWit(_,w1)   , TN_UWit(_,w2)   ) -> if w1 == w2 then po else
                                                (let (t1,b1) = w1 in
                                                 let (t2,b2) = w2 in
                                                 let po = eq_expr po t1 t2 in
                                                 eq_bndr po T b1 b2)
    | (TN_EWit(_,w1)   , TN_EWit(_,w2)   ) -> if w1 == w2 then po else
                                                (let (t1,b1) = w1 in
                                                 let (t2,b2) = w2 in
                                                 let po = eq_expr po t1 t2 in
                                                 eq_bndr po T b1 b2)
    | (TN_ITag(n1)     , TN_ITag(n2)     ) -> if n1 <> n2 then raise NoUnif; po
    | (TN_HApp(e1)     , TN_HApp(e2)     ) -> if not (eq_ho_appl e1 e2) then raise NoUnif; po
    | (TN_Goal(t1)     , TN_Goal(t2)     ) -> eq_expr po t1 t2
    | (TN_UVar(v1)     , _               ) -> let (p, po) = canonical_term p2 po in
                                              uvar_set v1 p;
                                              union (Ptr.T_ptr p1) (Ptr.T_ptr p2) po
    | (_               , TN_UVar(v2)     ) -> let (p, po) = canonical_term p1 po in
                                              uvar_set v2 p;
                                              union (Ptr.T_ptr p1) (Ptr.T_ptr p2) po
    | (_               , _               ) -> raise NoUnif

and eq_val : pool ref -> valu -> valu -> bool = fun pool v1 v2 ->
  if v1.elt == v2.elt then true else
    begin
      let po = !pool in
      log2 "eq_val: inserting %a = %a in context\n%a" Print.ex v1
           Print.ex v2 (print_pool "        ") po;
      let (p1, po) = add_valu po v1 in
      let (p2, po) = add_valu po v2 in
      log2 "eq_val: insertion at %a and %a" VPtr.print p1 VPtr.print p2;
      log2 "eq_val: obtained context:\n%a" (print_pool "        ") po;
      try pool := (Timed.apply (unif_vptr po p1) p2); true
      with NoUnif -> false
    end

and eq_trm : pool ref -> term -> term -> bool = fun pool t1 t2 ->
  if t1.elt == t2.elt then true else
    begin
      let po = !pool in
      log2 "eq_trm: inserting %a = %a in context\n%a" Print.ex t1
          Print.ex t2 (print_pool "        ") po;
      let (p1, po) = add_term po t1 in
      let (p2, po) = add_term po t2 in
      log2 "eq_trm: insertion at %a and %a" TPtr.print p1 TPtr.print p2;
      log2 "eq_trm: obtained context:\n%a" (print_pool "        ") po;
      try pool := (Timed.apply (unif_tptr po p1) p2); true
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
  if eq_expr ~strict:true t u then
    begin
      log2 "add_equiv: trivial proof";
      {pool}
    end
  else
  let (pt, pool) = add_term pool t in
  let (pu, pool) = add_term pool u in
  log2 "add_equiv: insertion at %a and %a" TPtr.print pt TPtr.print pu;
  log2 "add_equiv: obtained context:\n%a" (print_pool "        ") pool;
  let (pt, pool) = normalise pt pool in
  let (pu, pool) = normalise pu pool in
  let pool = union pt pu pool in
  log2 "add_equiv: normalisation to %a and %a after union"
          Ptr.print pt Ptr.print pu;
  log2 "add_equiv: obtained context:\n%a" (print_pool "        ") pool;
  {pool}

let add_vptr_nobox : VPtr.t -> pool -> pool = fun vp po ->
  let (vp, po) = find (Ptr.V_ptr vp) po in
  match vp with
  | Ptr.T_ptr(_) -> assert false
  | Ptr.V_ptr(vp) ->
     let po = { po with bs = VPtrSet.add vp po.bs } in
     let nps = parents (Ptr.V_ptr vp) po in
     PtrSet.fold reinsert nps po

let add_nobox : valu -> pool -> pool = fun v po ->
  log2 "add_nobox: inserting %a not box in context\n%a" Print.ex v
    (print_pool "        ") po;
  let (vp, po) = add_valu po v in
  add_vptr_nobox vp po

(* Adds an inequivalence to a context, producing a bigger context. The
   exception [Contradiction] is raised when expected. *)
let add_inequiv : inequiv -> eq_ctxt -> eq_ctxt = fun (t,u) {pool} ->
  log2 "add_inequiv: inserting %a ≠ %a in context\n%a" Print.ex t
    Print.ex u (print_pool "        ") pool;
  if eq_expr ~strict:true t u then
    begin
      log2 "immediate contradiction";
      bottom ()
    end;
  let (pt, pool) = add_term pool t in
  let (pu, pool) = add_term pool u in
  log2 "add_inequiv: insertion at %a and %a" TPtr.print pt TPtr.print pu;
  log2 "add_inequiv: obtained context:\n%a" (print_pool "        ") pool;
  let (pt, pool) = normalise pt pool in
  let (pu, pool) = normalise pu pool in
  log2 "add_inequiv: normalisation to %a and %a" Ptr.print pt Ptr.print pu;
  log2 "add_inequiv: obtained context:\n%a" (print_pool "        ") pool;
  try
    ignore (Timed.apply (unif_ptr pool pt) pu);
    log2 "add_inequiv: contradiction found";
    bottom ()
  with NoUnif -> {pool} (* TODO #51 store clauses *)

(* Main module interface. *)

(* epsilon for projection:
   proj_eps v l define a value w such v.l = w *)
let proj_eps : valu -> string -> valu = fun v l ->
  let eq x = equiv (valu None (vari None x))
                   true
                   (proj None (box v) (Pos.none l))
  in
  let bndr x = rest None unit_prod (eq x) in
  let t = Pos.none (Valu(Pos.none (Reco A.empty))) in
  ewit V t (None, unbox (vbind (mk_free V) "x" bndr))

let find_proj : pool -> valu -> string -> valu * pool = fun po v l ->
  try
    let (vp, po) = add_valu po v in
    let (vp, po) = find (Ptr.V_ptr vp) po in
    match vp with
    | Ptr.T_ptr(_) -> assert false (* Should never happen. *)
    | Ptr.V_ptr(vp) ->
       let (_, n) = find_v_node vp po in
       let (wp, w, po) =
         match n with
         | VN_Reco(m) ->
            let pt = A.find l m in
            (pt, Pos.none (VPtr pt), po)
         | _ ->
            let w = proj_eps v l in
            let (wp, po) = add_valu po w in
            let (pt, po) = add_term po (Pos.none (Proj(v,Pos.none l))) in
            let po = union (Ptr.V_ptr wp) (Ptr.T_ptr pt) po in
            (wp, w, po)
       in
       let po = if (VPtrSet.mem vp po.bs) then add_vptr_nobox wp po else po in
       (w, po)
  with e -> bug_msg "unexpected exception in find_proj: %s"
                    (Printexc.to_string e);
            assert false


(* NOTE: sum with one case should not fail, and be treated as projection *)
let find_sum : pool -> valu -> (string * valu * pool) option = fun po v ->
  try
    let (vp, po) = add_valu po v in
    let (vp, po) = find (Ptr.V_ptr vp) po in
    match vp with
      | Ptr.T_ptr(_) -> raise Not_found
      | Ptr.V_ptr(vp) ->
         let (_, n) = find_v_node vp po in
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
  let (vp, pool) = add_valu pool v in
  let (vp, pool) = find (Ptr.V_ptr vp) pool in
  match vp with
  | Ptr.T_ptr(_)  -> (false, {pool})
  | Ptr.V_ptr(vp) -> (VPtrSet.mem vp pool.bs, { pool })

(* Test whether a term is equivalent to a value or not. *)
let is_value : term -> eq_ctxt -> bool * eq_ctxt = fun t {pool} ->
  log2 "inserting %a not box in context\n%a" Print.ex t
    (print_pool "        ") pool;
  let (pt, pool) = add_term pool t in
  log2 "insertion at %a" TPtr.print pt;
  log2 "obtained context:\n%a" (print_pool "        ") pool;
  let (pt, pool) = normalise pt pool in
  let res = match pt with Ptr.V_ptr(_) -> true | Ptr.T_ptr(_) -> false in
  log2 "normalisation to %a" Ptr.print pt;
  log2 "obtained context:\n%a" (print_pool "        ") pool;
  log "%a is%s a value" Print.ex t (if res then "" else " not");
  (res, {pool})

(* Test whether a term is equivalent to a value or not. *)
let to_value : term -> eq_ctxt -> valu option * eq_ctxt = fun t {pool} ->
  let (pt, pool) = add_term pool t in
  let (pt, pool) = normalise pt pool in
  match pt with
  | Ptr.V_ptr(v) ->
     Some (Pos.none (VPtr v)), { pool }
  | Ptr.T_ptr(_) -> None, { pool }

let learn : eq_ctxt -> rel -> eq_ctxt = fun ctx rel ->
  log "learning %a" Print.rel rel;
  try
    let ctx =
      match rel with
      | Equiv(t,b,u) ->
         (if b then add_equiv else add_inequiv) (t,u) ctx
      | Posit _ -> assert false (* TODO #32 *)
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
      | Posit _ -> assert false (* TODO #32 *)
      | NoBox(v) ->
         let (b, ctx) = check_nobox v ctx in
         if b then raise Contradiction
    end;
    log "failed to prove %a" Print.rel rel;
    equiv_error rel
  with Contradiction ->
    log "proved   %a" Print.rel rel;
    ctx

let learn ctx rel = Chrono.add_time equiv_chrono (learn ctx) rel
let prove ctx rel = Chrono.add_time equiv_chrono (prove ctx) rel
let to_value t eqs = Chrono.add_time equiv_chrono (to_value t) eqs
let is_value t eqs = Chrono.add_time equiv_chrono (is_value t) eqs
let check_nobox v eqs = Chrono.add_time equiv_chrono (check_nobox v) eqs
let add_nobox v eqs = Chrono.add_time equiv_chrono (add_nobox v) eqs
let find_proj eqs v = Chrono.add_time equiv_chrono (find_proj eqs) v
let find_sum eqs v = Chrono.add_time equiv_chrono (find_sum eqs) v
