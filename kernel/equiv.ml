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
open ExprInfo
open Compare

(* Log function registration. *)
let log_edp = Log.register 'e' (Some "equ") "equivalence decision procedure"
let log_edp = Log.(log_edp.p)

(** Exception raise when the pool contains a contradiction. *)
exception Contradiction
let bottom () = raise Contradiction

(** Module for pointers on a value node of the graph. *)
module VPtr =
  struct
    type t = V of int
    let compare (V i) (V j) = i - j
    let print ch (V i) = Printf.fprintf ch "%i" i
  end
module VPtrMap = Map.Make(VPtr)
module VPtrSet = Set.Make(VPtr)

(** Module for pointers on a term node of the graph. *)
module TPtr =
  struct
    type t = T of int
    let compare (T i) (T j) = i - j
    let print ch (T i) = Printf.fprintf ch "%i" i
  end
module TPtrMap = Map.Make(TPtr)

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

(** Type of a pointer map, used to keep track of equivalences. *)
type eq_map = Ptr.t PtrMap.t

(** Wrapper for higher-order application. *)
type _ ho_appl =
  | HO_Appl : 'a sort * ('a -> 'b) ex loc * 'a ex loc -> 'b ho_appl

(** Type of a value node. *)
type v_node =
  | VN_LAbs of (v, t) bndr
  | VN_Cons of A.key loc * VPtr.t
  | VN_Reco of VPtr.t A.t
  | VN_Scis
  | VN_VWit of ((v, t) bndr * (v, p) bndr * p ex loc)
  | VN_UWit of (t ex loc * (v, p) bndr)
  | VN_EWit of (t ex loc * (v, p) bndr)
  | VN_HApp of v ho_appl
  | VN_UVar of v uvar
  | VN_ITag of int
type v_map = (PtrSet.t * v_node) VPtrMap.t
type b_map = VPtrSet.t

(** Type of a term node. *)
type t_node =
  | TN_Valu of VPtr.t
  | TN_Appl of TPtr.t * TPtr.t
  | TN_MAbs of (s, t) bndr
  | TN_Name of s ex loc * TPtr.t
  | TN_Proj of VPtr.t * A.key loc
  | TN_Case of VPtr.t * (v, t) bndr A.t
  | TN_FixY of TPtr.t * VPtr.t
  | TN_UWit of (t ex loc * (t, p) bndr)
  | TN_EWit of (t ex loc * (t, p) bndr)
  | TN_HApp of t ho_appl
  | TN_UVar of t uvar
  | TN_ITag of int
type t_map = (PtrSet.t * t_node) TPtrMap.t

(** Printing function for value nodes. *)
let print_v_node : out_channel -> v_node -> unit = fun ch n ->
  let prnt = Printf.fprintf in
  let pex = Print.print_ex in
  match n with
  | VN_LAbs(b)     -> prnt ch "VN_LAbs(%a)" pex (Pos.none (LAbs(None,b)))
  | VN_Cons(c,pv)  -> prnt ch "VN_Cons(%s,%a)" c.elt VPtr.print pv
  | VN_Reco(m)     -> let pelt ch (k, p) = prnt ch "%S=%a" k VPtr.print p in
                      prnt ch "VN_Reco(%a)" (Print.print_map pelt ":") m
  | VN_Scis        -> prnt ch "VN_Scis"
  | VN_VWit(b,_,_) -> prnt ch "VN_VWit(ει%s)" (bndr_name b).elt
  | VN_UWit(_,b)   -> prnt ch "VN_UWit(ε∀%s)" (bndr_name b).elt
  | VN_EWit(_,b)   -> prnt ch "VN_EWit(ε∃%s)" (bndr_name b).elt
  | VN_HApp(e)     -> let HO_Appl(s,f,a) = e in
                      prnt ch "VN_HApp(%a)" pex (Pos.none (HApp(s,f,a)))
  | VN_UVar(v)     -> prnt ch "VN_UVar(%a)" pex (Pos.none (UVar(V,v)))
  | VN_ITag(n)     -> prnt ch "VN_ITag(%d)" n

(** Printing function for term nodes. *)
let print_t_node : out_channel -> t_node -> unit = fun ch n ->
  let prnt = Printf.fprintf in
  let pex = Print.print_ex in
  match n with
  | TN_Valu(pv)    -> prnt ch "TN_Valu(%a)" VPtr.print pv
  | TN_Appl(pt,pu) -> prnt ch "TN_Appl(%a,%a)" TPtr.print pt TPtr.print pu
  | TN_MAbs(b)     -> prnt ch "TN_MAbs(%a)" pex (Pos.none (MAbs b))
  | TN_Name(s,pt)  -> prnt ch "TN_Name(%a,%a)" pex s TPtr.print pt
  | TN_Proj(pv,l)  -> prnt ch "TN_Proj(%a,%s)" VPtr.print pv  l.elt
  | TN_Case(pv,m)  -> let pelt ch (k, b) =
                        prnt ch "%S → %a" k pex (Pos.none (LAbs(None,b)))
                      in
                      let pmap = Print.print_map pelt "|" in
                      prnt ch "TN_Case(%a|%a)" VPtr.print pv pmap m
  | TN_FixY(pt,pv) -> prnt ch "TN_FixY(%a,%a)" TPtr.print pt VPtr.print pv
  | TN_UWit(_,b)   -> prnt ch "TN_UWit(ε∀%s)" (bndr_name b).elt
  | TN_EWit(_,b)   -> prnt ch "TN_EWit(ε∃%s)" (bndr_name b).elt
  | TN_HApp(e)     -> let HO_Appl(s,f,a) = e in
                      let e = Pos.none (HApp(s,f,a)) in
                      prnt ch "TN_HApp(%a)" Print.print_ex e
  | TN_UVar(v)     -> prnt ch "TN_UVar(%a)" pex (Pos.none (UVar(T,v)))
  | TN_ITag(n)     -> prnt ch "TN_ITag(%d)" n

(** Type of a pool. *)
type pool =
  { vs     : v_map
  ; ts     : t_map
  ; bs     : b_map
  ; next   : int
  ; eq_map : eq_map }

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
  ; eq_map = PtrMap.empty }

(** Node search. *)
let find_v_node : VPtr.t -> pool -> PtrSet.t * v_node = fun p po ->
  VPtrMap.find p po.vs

let find_t_node : TPtr.t -> pool -> PtrSet.t * t_node = fun p po ->
  TPtrMap.find p po.ts

(** Geting the children sons of a node. *)

let children_v_node : v_node -> Ptr.t list = fun n ->
  match n with
  | VN_LAbs _
  | VN_Scis
  | VN_VWit _
  | VN_UWit _
  | VN_ITag _
  | VN_UVar _ (* TODO check *)
  | VN_HApp _ (* TODO check *)
  | VN_EWit _     -> []
  | VN_Cons(_,pv) -> [Ptr.V_ptr pv]
  | VN_Reco(m)    -> A.fold (fun _ p s -> Ptr.V_ptr p :: s) m []

let children_t_node : t_node -> Ptr.t list = fun n ->
  match n with
  | TN_Valu(pv)    -> [Ptr.V_ptr pv]
  | TN_Appl(pt,pu) -> [Ptr.T_ptr pt; Ptr.T_ptr pu]
  | TN_Name(_,pt)  -> [Ptr.T_ptr pt]
  | TN_Proj(pv,_)  -> [Ptr.V_ptr pv]
  | TN_Case(pv,_)  -> [Ptr.V_ptr pv]
  | TN_FixY(pt,pv) -> [Ptr.T_ptr pt; Ptr.V_ptr pv]
  | TN_MAbs _
  | TN_UWit _
  | TN_EWit _
  | TN_HApp _
  | TN_ITag _
  | TN_UVar _      -> []

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

let add_parent_v_nodes : VPtr.t -> Ptr.t list -> pool -> pool = fun vp ps po ->
  add_parent_nodes (Ptr.V_ptr vp) ps po

let add_parent_t_nodes : TPtr.t -> Ptr.t list -> pool -> pool = fun tp ps po ->
  add_parent_nodes (Ptr.T_ptr tp) ps po

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

(** Equality functions on nodes. *)
let eq_v_nodes : pool -> v_node -> v_node -> bool = fun po n1 n2 -> n1 == n2 ||
  let eq_expr e1 e2 = eq_expr ~strict:true e1 e2 in
  let eq_bndr b1 b2 = eq_bndr ~strict:true b1 b2 in
  match (n1, n2) with
  | (VN_LAbs(b1)   , VN_LAbs(b2)   ) -> eq_bndr V b1 b2
  | (VN_Cons(c1,p1), VN_Cons(c2,p2)) -> c1.elt = c2.elt && eq_vptr po p1 p2
  | (VN_Reco(m1)   , VN_Reco(m2)   ) -> A.equal (eq_vptr po) m1 m2
  | (VN_Scis       , VN_Scis       ) -> true
  | (VN_VWit(w1)   , VN_VWit(w2)   ) -> let (f1,a1,b1) = w1 in
                                        let (f2,a2,b2) = w2 in
                                        eq_bndr V f1 f2 && eq_bndr V a1 a2 &&
                                        eq_expr b1 b2
  | (VN_UWit(t1,b1), VN_UWit(t2,b2)) -> eq_expr t1 t2 && eq_bndr V b1 b2
  | (VN_EWit(t1,b1), VN_EWit(t2,b2)) -> eq_expr t1 t2 && eq_bndr V b1 b2
  | (VN_ITag(n1)   , VN_ITag(n2)   ) -> n1 = n2
  | (_             , _             ) -> false

let eq_t_nodes : pool -> t_node -> t_node -> bool = fun po n1 n2 -> n1 == n2 ||
  let eq_expr e1 e2 = eq_expr ~strict:true e1 e2 in
  let eq_bndr b1 b2 = eq_bndr ~strict:true b1 b2 in
  match (n1, n2) with
  | (TN_Valu(p1)     , TN_Valu(p2)     ) -> eq_vptr po p1 p2
  | (TN_Appl(p11,p12), TN_Appl(p21,p22)) -> eq_tptr po p11 p21 &&
                                              eq_tptr po p12 p22
  | (TN_MAbs(b1)     , TN_MAbs(b2)     ) -> eq_bndr S b1 b2
  | (TN_Name(s1,p1)  , TN_Name(s2,p2)  ) -> eq_expr s1 s2 && eq_tptr po p1 p2
  | (TN_Proj(p1,l1)  , TN_Proj(p2,l2)  ) -> eq_vptr po p1 p2 && l1.elt = l2.elt
  | (TN_Case(p1,m1)  , TN_Case(p2,m2)  ) -> eq_vptr po p1 p2 &&
                                              A.equal (eq_bndr V) m1 m2
  | (TN_FixY(p11,p12), TN_FixY(p21,p22)) -> eq_tptr po p11 p21 &&
                                              eq_vptr po p12 p22
  | (TN_UWit(t1,b1)  , TN_UWit(t2,b2)  ) -> eq_expr t1 t2 && eq_bndr T b1 b2
  | (TN_EWit(t1,b1)  , TN_EWit(t2,b2)  ) -> eq_expr t1 t2 && eq_bndr T b1 b2
  | (TN_ITag(n1)     , TN_ITag(n2)     ) -> n1 = n2
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
  | VN_ITag _ -> false

(** Insertion function for nodes. *)
exception FoundV of VPtr.t
let insert_v_node : v_node -> pool -> VPtr.t * pool = fun nn po ->
  let fn p (_,n) = if eq_v_nodes po n nn then raise (FoundV p) in
  try VPtrMap.iter fn po.vs; raise Not_found with
  | FoundV(p) -> (p, po)
  | Not_found ->
      let ptr = VPtr.V po.next in
      let vs = VPtrMap.add ptr (PtrSet.empty, nn) po.vs in
      let next = po.next + 1 in
      let bs = if immediate_nobox nn then VPtrSet.add ptr po.bs else po.bs in
      let po = { po with vs ; bs; next } in
      let children = children_v_node nn in
      let po = add_parent_v_nodes ptr children po in
      (ptr, po)

exception FoundT of TPtr.t
let insert_t_node : t_node -> pool -> TPtr.t * pool = fun nn po ->
  let fn p (_,n) = if eq_t_nodes po n nn then raise (FoundT p) in
  try TPtrMap.iter fn po.ts; raise Not_found with
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
      let children = children_t_node nn in
      let po = add_parent_t_nodes ptr children po in
      (ptr, po)

(** Insertion of actual terms and values to the pool. *)
let rec add_term : pool -> term -> TPtr.t * pool = fun po t ->
  match (Norm.whnf t).elt with
  | Valu(v)     -> let (pv, po) = add_valu po v in
                   let (pp, po) = insert_t_node (TN_Valu(pv)) po in
                   (pp, po)
  | Appl(t,u)   -> let (pt, po) = add_term po t in
                   let (pu, po) = add_term po u in
                   let (pp, po) = insert_t_node (TN_Appl(pt,pu)) po in
                   (pp, po)
  | MAbs(b)     -> insert_t_node (TN_MAbs(b)) po
  | Name(s,t)   -> let (pt, po) = add_term po t in
                   let (pp, po) = insert_t_node (TN_Name(s,pt)) po in
                   (pp, po)
  | Proj(v,l)   -> let (pv, po) = add_valu po v in
                   let (pp, po) = insert_t_node (TN_Proj(pv,l)) po in
                   (pp, po)
  | Case(v,m)   -> let (pv, po) = add_valu po v in
                   let m = A.map snd m in
                   let (pp, po) = insert_t_node (TN_Case(pv,m)) po in
                   (pp, po)
  | FixY(t,v)   -> let (pt, po) = add_term po t in
                   let (pv, po) = add_valu po v in
                   let (pp, po) = insert_t_node (TN_FixY(pt,pv)) po in
                   (pp, po)
  | TTyp(t,_)   -> add_term po t
  | TLam(_,b)   -> add_term po (bndr_subst b Dumm)
  | UWit(_,t,b) -> insert_t_node (TN_UWit((t,b))) po
  | EWit(_,t,b) -> insert_t_node (TN_EWit((t,b))) po
  | HApp(s,f,a) -> insert_t_node (TN_HApp(HO_Appl(s,f,a))) po
  | HDef(_,d)   -> add_term po d.expr_def
  | UVar(_,v)   -> insert_t_node (TN_UVar(v)) po
  | ITag(_,n)   -> insert_t_node (TN_ITag(n)) po
  | Goal(_)     -> failwith "goal in the pool (term)"
  | Vari(_)     -> invalid_arg "free variable in the pool"
  | Dumm        -> invalid_arg "dummy terms forbidden in the pool"

and     add_valu : pool -> valu -> VPtr.t * pool = fun po v ->
  match (Norm.whnf v).elt with
  | LAbs(_,b)   -> insert_v_node (VN_LAbs(b)) po
  | Cons(c,v)   -> let (pv, po) = add_valu po v in
                   let (pp, po) = insert_v_node (VN_Cons(c,pv)) po in
                   (pp, po)
  | Reco(m)     -> let fn l (_, v) (m, po) =
                     let (pv, po) = add_valu po v in
                     (A.add l pv m, po)
                   in
                   let (m, po) = A.fold fn m (A.empty, po) in
                   let (pp, po) = insert_v_node (VN_Reco(m)) po in
                   (pp, po)
  | Scis        -> insert_v_node VN_Scis po
  | VDef(d)     -> add_valu po (Erase.to_valu d.value_eval)
  | VTyp(v,_)   -> add_valu po v
  | VLam(_,b)   -> add_valu po (bndr_subst b Dumm)
  | VWit(f,a,b) -> insert_v_node (VN_VWit(f,a,b)) po
  | UWit(_,t,b) -> insert_v_node (VN_UWit(t,b)) po
  | EWit(_,t,b) -> insert_v_node (VN_EWit(t,b)) po
  | HApp(s,f,a) -> insert_v_node (VN_HApp(HO_Appl(s,f,a))) po
  | HDef(_,d)   -> add_valu po d.expr_def
  | UVar(_,v)   -> insert_v_node (VN_UVar(v)) po
  | ITag(_,n)   -> insert_v_node (VN_ITag(n)) po

  | Goal(_)     -> failwith "goal in the pool (term)"
  | Vari(_)     -> invalid_arg "free variable in the pool"
  | Dumm        -> invalid_arg "dummy terms forbidden in the pool"

(* unused, but may be usefull for debugging
let rec to_term : TPtr.t -> pool -> term = fun p po ->
  let t =
    match snd (find_t_node p po) with
    | TN_Valu(pv)    -> Valu(to_valu pv po)
    | TN_Appl(pt,pu) -> Appl(to_term pt po, to_term pu po)
    | TN_MAbs(b)     -> MAbs(None, b)
    | TN_Name(s,pt)  -> Name(s, to_term pt po)
    | TN_Proj(pv,l)  -> Proj(to_valu pv po, l)
    | TN_Case(pv,m)  -> Case(to_valu pv po, M.map (fun b -> (None, b)) m)
    | TN_FixY(pt,pv) -> FixY(to_term pt po, to_valu pv po)
    | TN_UWit(w)     -> let (t,b) = w in UWit(T,t,b)
    | TN_EWit(w)     -> let (t,b) = w in EWit(T,t,b)
    | TN_HApp(e)     -> let HO_Appl(s,f,a) = e in HApp(s,f,a)
    | TN_UVar(v)     -> UVar(T,v)
  in Pos.none t

and     to_valu : VPtr.t -> pool -> valu = fun p po ->
  let v =
    match snd (find_v_node p po) with
    | VN_LAbs(b)     -> LAbs(None, b)
    | VN_Cons(c,pv)  -> Cons(c, to_valu pv po)
    | VN_Reco(m)     -> Reco(M.map (fun vp -> (None, to_valu vp po)) m)
    | VN_Scis        -> Scis
    | VN_VWit(w)     -> let (f,a,b) = w in VWit(f,a,b)
    | VN_UWit(w)     -> let (t,b) = w in UWit(V,t,b)
    | VN_EWit(w)     -> let (t,b) = w in EWit(V,t,b)
    | VN_HApp(e)     -> let HO_Appl(s,f,a) = e in HApp(s,f,a)
    | VN_UVar(v)     -> UVar(V,v)
  in Pos.none v *)

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
        | TN_MAbs(b)     -> (Pos.none (MAbs(b)), po)
        | TN_Name(s,pt)  -> let (t, po) = canonical_term pt po in
                            (Pos.none (Name(s,t)), po)
        | TN_Proj(pv,l)  -> let (v, po) = canonical_valu pv po in
                            (Pos.none (Proj(v,l)), po)
        | TN_Case(pv,m)  -> let (v, po) = canonical_valu pv po in
                            let t = Case(v, A.map (fun b -> (None, b)) m) in
                            (Pos.none t, po)
        | TN_FixY(pt,pv) -> let (t, po) = canonical_term pt po in
                            let (v, po) = canonical_valu pv po in
                            (Pos.none (FixY(t,v)), po)
        | TN_UWit(w)     -> let (t,b) = w in (Pos.none (UWit(T,t,b)), po)
        | TN_EWit(w)     -> let (t,b) = w in (Pos.none (EWit(T,t,b)), po)
        | TN_HApp(e)     -> let HO_Appl(s,f,a) = e in
                            (Pos.none (HApp(s,f,a)), po)
        | TN_UVar(v)     -> begin
                              match !(v.uvar_val) with
                              | None   -> (Pos.none (UVar(T,v)), po)
                              | Some t ->
                                  let (p, po) = add_term po t in
                                  canonical_term p po
                            end
        | TN_ITag(n)      -> (Pos.none (ITag(T,n)), po)
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
        | VN_LAbs(b)     -> (Pos.none (LAbs(None, b)), po)
        | VN_Cons(c,pv)  -> let (v, po) = canonical_valu pv po in
                            (Pos.none (Cons(c,v)), po)
        | VN_Reco(m)     -> let fn l pv (m, po) =
                              let (v, po) = canonical_valu pv po in
                              (A.add l (None,v) m, po)
                            in
                            let (m, po) = A.fold fn m (A.empty, po) in
                            (Pos.none (Reco(m)), po)
        | VN_Scis        -> (Pos.none Scis, po)
        | VN_VWit(w)     -> let (f,a,b) = w in (Pos.none (VWit(f,a,b)), po)
        | VN_UWit(w)     -> let (t,b) = w in (Pos.none (UWit(V,t,b)), po)
        | VN_EWit(w)     -> let (t,b) = w in (Pos.none (EWit(V,t,b)), po)
        | VN_HApp(e)     -> let HO_Appl(s,f,a) = e in
                            (Pos.none (HApp(s,f,a)), po)
        | VN_UVar(v)     -> begin
                              match !(v.uvar_val) with
                              | None   -> (Pos.none (UVar(V,v)), po)
                              | Some w ->
                                  let (p, po) = add_valu po w in
                                  canonical_valu p po
                            end
        | VN_ITag(n)      -> (Pos.none (ITag(V,n)), po)
      end

let canonical : Ptr.t -> pool -> term * pool = fun p po ->
  match p with
  | Ptr.T_ptr p -> canonical_term p po
  | Ptr.V_ptr p -> let (v, po) = canonical_valu p po in
                   (Pos.none (Valu v), po)

let err_msg = log_edp

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

(** Normalisation function. *)
let rec normalise : TPtr.t -> pool -> Ptr.t * pool =
  fun p po ->
    let (p, po) =
       match snd (TPtrMap.find p po.ts) with
       | TN_Valu(pv)    -> (Ptr.V_ptr pv, po)
       | TN_Appl(pt,pu) ->
          begin
            log_edp "normalise in TN_Appl: %a %a" TPtr.print pt TPtr.print pu;
            let (pt, po) = normalise pt po in
            let (pu, po) = normalise pu po in
             (* argument must be really normalised, even is update is true *)
            let (tp, po) = insert_appl pt pu po in
            let po = union (Ptr.T_ptr p)  tp po in
            log_edp "normalised in TN_Appl: %a %a => %a"
                    Ptr.print pt Ptr.print pu  Ptr.print tp;
            match (pt, pu) with
            | (Ptr.V_ptr pf, Ptr.V_ptr pv) ->
               begin
                 match snd (VPtrMap.find pf po.vs), VPtrSet.mem pv po.bs with
                 | VN_LAbs(b), true ->
                    begin
                      let (v, po) = canonical_valu pv po in
                      let t = bndr_subst b v.elt in
                      let (tp, po) = add_term po t in
                      let po = union (Ptr.T_ptr p) (Ptr.T_ptr tp) po in
                      normalise tp po
                    end
                 | _          ->
                    log_edp "normalised insert(1) TN_Appl: %a" Ptr.print tp;
                    (tp, po)
               end
            | (_           , _           ) ->
               log_edp "normalised insert(2) TN_Appl: %a" Ptr.print tp;
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
            log_edp "normalisation in TN_Case: %a" VPtr.print pv;
            match snd (VPtrMap.find pv po.vs) with
            | VN_Cons(c,pv) ->
               begin
                 try
                   let (v, po) = canonical_valu pv po in
                   let t = bndr_subst (A.find c.elt m) v.elt in
                   let (tp, po) = add_term po t in
                   let po = union (Ptr.T_ptr p) (Ptr.T_ptr tp) po in
                   normalise tp po
                 with
                   Not_found -> (Ptr.T_ptr p, po)
               end
            | _            -> (Ptr.T_ptr p, po)
          end
       | TN_FixY(pt,pv) ->
          begin
            let (t, po) = canonical_term pt po in
            let b = bndr_from_fun "x" (fun x -> FixY(t, Pos.none x)) in
            let (pf, po) = insert_v_node (VN_LAbs(b)) po in
            let (pf, po) = insert_t_node (TN_Valu(pf)) po in
            let (pap, po) = insert_t_node (TN_Appl(pt, pf)) po in
            let (pu, po) = insert_t_node (TN_Valu(pv)) po in
            let (pap, po) = insert_t_node (TN_Appl(pap, pu)) po in
            let po = union (Ptr.T_ptr p) (Ptr.T_ptr pap) po in
            normalise pap po
          end
       | TN_UWit(_)     -> (Ptr.T_ptr p, po)
       | TN_EWit(_)     -> (Ptr.T_ptr p, po)
       | TN_HApp(_)     -> (Ptr.T_ptr p, po)
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
    find p po

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
          log_edp "normalisation of parent %a" TPtr.print tp;
          let (p', po) = normalise tp po in
          log_edp "normalised parent %a at %a" TPtr.print tp Ptr.print p';
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
  if p2 < p1 then join p1 p2 po else join p2 p1 po

and union : Ptr.t -> Ptr.t -> pool -> pool = fun p1 p2 po ->
  let (p1, po) = find p1 po in
  let (p2, po) = find p2 po in
  if p1 = p2 then po else
    match (p1, p2) with
    | (Ptr.T_ptr _  , Ptr.V_ptr _  ) -> join p1 p2 po
    | (Ptr.V_ptr _  , Ptr.T_ptr _  ) -> join p2 p1 po
    | (Ptr.T_ptr _  , Ptr.T_ptr _  ) -> join p1 p2 po
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

(* Log functions registration. *)
let log_ora = Log.register 'o' (Some "ora") "oracle informations"
let log_ora = Log.(log_ora.p)

let is_equal : pool -> Ptr.t -> Ptr.t -> bool = fun po p1 p2 ->
  if Ptr.compare p1 p2 = 0 then true else
  let (p1, po) = find p1 po in
  let (p2, po) = find p2 po in
  if Ptr.compare p1 p2 = 0 then true else
  let (t1, po) = canonical p1 po in
  let (t2, po) = canonical p2 po in
  log_edp "test term equality %a = %a" Print.print_ex t1 Print.print_ex t2;
  eq_expr t1 t2

(* Equational context type. *)
type eq_ctxt =
  { pool : pool }

let empty_ctxt : eq_ctxt =
  { pool = empty_pool }

type equiv   = term * term
type inequiv = term * term

let eq_val : eq_ctxt -> valu -> valu -> bool = fun {pool} v1 v2 ->
  if v1 == v2 then true else begin
  log_edp "eq_val: inserting %a = %a in context\n%a" Print.print_ex v1
          Print.print_ex v2 (print_pool "        ") pool;
  let (p1, pool) = add_valu pool v1 in
  let (p2, pool) = add_valu pool v2 in
  log_edp "eq_val: insertion at %a and %a" VPtr.print p1 VPtr.print p2;
  log_edp "eq_val: obtained context:\n%a" (print_pool "        ") pool;
  if VPtr.compare p1 p2 = 0 then true else
  let (t1, pool) = canonical (Ptr.V_ptr p1) pool in
  let (t2, pool) = canonical (Ptr.V_ptr p2) pool in
  log_edp "eq_val: test %a = %a" Print.print_ex t1 Print.print_ex t2;
  eq_expr t1 t2 end

let eq_trm : eq_ctxt -> term -> term -> bool = fun {pool} t1 t2 ->
  if t1 == t2 then true else begin
  log_edp "eq_trm: inserting %a = %a in context\n%a" Print.print_ex t1
          Print.print_ex t2 (print_pool "        ") pool;
  let (p1, pool) = add_term pool t1 in
  let (p2, pool) = add_term pool t2 in
  log_edp "eq_trm: insertion at %a and %a" TPtr.print p1 TPtr.print p2;
  log_edp "eq_trm: obtained context:\n%a" (print_pool "        ") pool;
  if TPtr.compare p1 p2 = 0 then true else
  let (t1, pool) = canonical (Ptr.T_ptr p1) pool in
  let (t2, pool) = canonical (Ptr.T_ptr p2) pool in
  log_edp "eq_trm: %a = %a" Print.print_ex t1 Print.print_ex t2;
  eq_expr t1 t2 end

(* Adds an equivalence to a context, producing a bigger context. The
   exception [Contradiction] is raised when expected. *)
let add_equiv : equiv -> eq_ctxt -> eq_ctxt = fun (t,u) {pool} ->
  log_edp "add_equiv: inserting %a = %a in context\n%a" Print.print_ex t
    Print.print_ex u (print_pool "        ") pool;
  if eq_expr ~strict:true t u then
    begin
      log_edp "add_equiv: trivial proof";
      {pool}
    end
  else
  let (pt, pool) = add_term pool t in
  let (pu, pool) = add_term pool u in
  log_edp "add_equiv: insertion at %a and %a" TPtr.print pt TPtr.print pu;
  log_edp "add_equiv: obtained context:\n%a" (print_pool "        ") pool;
  let (pt, pool) = normalise pt pool in
  let (pu, pool) = normalise pu pool in
  let pool = union pt pu pool in
  log_edp "add_equiv: normalisation to %a and %a after union"
          Ptr.print pt Ptr.print pu;
  log_edp "add_equiv: obtained context:\n%a" (print_pool "        ") pool;
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
  log_edp "add_nobox: inserting %a not box in context\n%a" Print.print_ex v
    (print_pool "        ") po;
  let (vp, po) = add_valu po v in
  add_vptr_nobox vp po

(* Adds an inequivalence to a context, producing a bigger context. The
   exception [Contradiction] is raised when expected. *)
let add_inequiv : inequiv -> eq_ctxt -> eq_ctxt = fun (t,u) {pool} ->
  log_edp "add_inequiv: inserting %a ≠ %a in context\n%a" Print.print_ex t
    Print.print_ex u (print_pool "        ") pool;
  if eq_expr ~strict:true t u then
    begin
      log_edp "immediate contradiction";
      bottom ()
    end;
  let (pt, pool) = add_term pool t in
  let (pu, pool) = add_term pool u in
  log_edp "add_inequiv: insertion at %a and %a" TPtr.print pt TPtr.print pu;
  log_edp "add_inequiv: obtained context:\n%a" (print_pool "        ") pool;
  let (pt, pool) = normalise pt pool in
  let (pu, pool) = normalise pu pool in
  log_edp "add_inequiv: normalisation to %a and %a" Ptr.print pt Ptr.print pu;
  log_edp "add_inequiv: obtained context:\n%a" (print_pool "        ") pool;
  if is_equal pool pt pu then
    begin
      log_edp "add_inequiv: contradiction found";
      bottom ()
    end;
  {pool} (* TODO store clauses *)

(* Main module interface. *)

(* epsilon for projection:
   proj_eps v l define a value w such v.l = w *)
let proj_eps : valu -> string -> valu = fun v l ->
  let eq x = equiv (valu None (vari None x))
                   true
                   (proj None (box v) (Pos.none l))
  in
  let bndr x = rest None unit_prod (eq x) in
  unbox (ewit None (valu None unit_reco) (Pos.none "x") V bndr)

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
            let (w, po) = canonical_valu pt po in
            (pt, w, po)
         | _ ->
            let w = proj_eps v l in
            let (wp, po) = add_valu po w in
            let (pt, po) = add_term po (Pos.none (Proj(v,Pos.none l))) in
            let po = union (Ptr.V_ptr wp) (Ptr.T_ptr pt) po in
            (wp, w, po)
       in
       let po = if (VPtrSet.mem vp po.bs) then add_vptr_nobox wp po else po in
       (w, po)

  with Not_found -> assert false (* TODO: check, could be a contradiction *)

(* TODO: sum with one case should not fail *)
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
            let v, po = canonical_valu pt po in
            Some (c.elt, v, po)
         | _ -> raise Not_found
  with Not_found -> None


type relation = cond

(* TODO share with print.ml *)
let print_relation = fun ch -> let open Printf in let open Print in
  function
    | Equiv(t,b,u) -> let sym = if b then "=" else "≠" in
                      fprintf ch "%a %s %a" print_ex t sym print_ex u
    | NoBox(v)     -> fprintf ch "%a↓" print_ex v
    | Posit(o)     -> print_ex ch o

(* TODO share with print.ml *)
let print_relation_pos : out_channel -> relation -> unit = fun ch c ->
  match c with
  | Equiv (t,b,u) ->
     begin
       match t.pos with
       | None   -> Print.print_ex ch t
       | Some p -> Printf.fprintf ch "(%a)" print_short_pos p
     end;
     output_string ch (if b then " = " else " ≠ ");
     begin
       match u.pos with
       | None   -> Print.print_ex ch u
       | Some p -> Printf.fprintf ch "(%a)" print_short_pos p
     end
  | NoBox(v) ->
     begin
       match v.pos with
       | None   -> Print.print_ex ch v
       | Some p -> Printf.fprintf ch "(%a)" print_short_pos p
     end
  | Posit _ -> assert false

exception Failed_to_prove of relation
let equiv_error : relation -> 'a =
  fun rel -> raise (Failed_to_prove rel)

(* Adds no box to the bool *)
let check_nobox : valu -> eq_ctxt -> bool * eq_ctxt = fun v {pool} ->
  log_edp "inserting %a not box in context\n%a" Print.print_ex v
    (print_pool "        ") pool;
  let (vp, pool) = add_valu pool v in
  let (vp, pool) = find (Ptr.V_ptr vp) pool in
  match vp with
  | Ptr.T_ptr(_) -> (false, {pool})
  | Ptr.V_ptr(vp) -> (VPtrSet.mem vp pool.bs, { pool })

(* Test whether a term is equivalent to a value or not. *)
let is_value : term -> eq_ctxt -> bool * eq_ctxt = fun t {pool} ->
  log_edp "inserting %a not box in context\n%a" Print.print_ex t
    (print_pool "        ") pool;
  let (pt, pool) = add_term pool t in
  log_edp "insertion at %a" TPtr.print pt;
  log_edp "obtained context:\n%a" (print_pool "        ") pool;
  let (pt, pool) = normalise pt pool in
  let res = match pt with Ptr.V_ptr(_) -> true | Ptr.T_ptr(_) -> false in
  log_edp "normalisation to %a" Ptr.print pt;
  log_edp "obtained context:\n%a" (print_pool "        ") pool;
  log_edp "%a is%s a value" Print.print_ex t (if res then "" else " not");
  (res, {pool})

(* Test whether a term is equivalent to a value or not. *)
let to_value : term -> eq_ctxt -> (valu * eq_ctxt) option = fun t {pool} ->
  let (pt, pool) = add_term pool t in
  let (pt, pool) = normalise pt pool in
  match pt with
  | Ptr.V_ptr(v) ->
     let (v, pool) = canonical_valu v pool in
     Some (v, { pool })
  | Ptr.T_ptr(_) -> None (* FIXME #47 keep the pool in this case too *)

let learn : eq_ctxt -> relation -> eq_ctxt = fun ctx rel ->
  log_edp "learning %a" print_relation rel;
  try
    let ctx =
      match rel with
      | Equiv(t,b,u) ->
         (if b then add_equiv else add_inequiv) (t,u) ctx
      | Posit _ -> assert false (* TODO *)
      | NoBox(v) ->
         {pool = add_nobox v ctx.pool }
    in
    log_edp "learned  %a" print_relation rel; ctx
  with Contradiction ->
    log_edp "contradiction in the context";
    raise Contradiction

let prove : eq_ctxt -> relation -> eq_ctxt = fun ctx rel ->
  log_edp "proving  %a" print_relation rel;
  try
    begin
      match rel with
      | Equiv(t,b,u) ->
         ignore ((if b then add_inequiv else add_equiv) (t,u) ctx);
      | Posit _ -> assert false (* TODO *)
      | NoBox(v) ->
         let (b, ctx) = check_nobox v ctx in
         if b then raise Contradiction
    end;
    log_edp "failed to prove %a" print_relation rel;
    equiv_error rel
  with Contradiction ->
    log_edp "proved   %a" print_relation rel;
    ctx
