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
module PtrMap  = Map.Make(Ptr)

(** Type of a pointer map, used to keep track of equivalences. *)
type eq_map = Ptr.t PtrMap.t

(** Type of a value node. *)
type v_node =
  | VN_Vari of v var
  | VN_LAbs of (v, t) bndr
  | VN_Cons of M.key loc * VPtr.t
  | VN_Reco of VPtr.t M.t
  | VN_Scis
  | VN_VWit of ((v, t) bndr * p ex loc * p ex loc)
  | VN_UWit of (t ex loc * (v, p) bndr)
  | VN_EWit of (t ex loc * (v, p) bndr)
type v_map = (Ptr.t list * v_node) VPtrMap.t

(** Type of a term node. *)
type t_node =
  | TN_Vari of t var
  | TN_Valu of VPtr.t
  | TN_Appl of TPtr.t * TPtr.t
  | TN_MAbs of (s, t) bndr
  | TN_Name of s ex loc * TPtr.t
  | TN_Proj of VPtr.t * M.key loc
  | TN_Case of VPtr.t * (v, t) bndr M.t
  | TN_FixY of TPtr.t * VPtr.t
  | TN_UWit of (t ex loc * (t, p) bndr)
  | TN_EWit of (t ex loc * (t, p) bndr)
type t_map = (Ptr.t list * t_node) TPtrMap.t

(** Printing function for value nodes. *)
let print_v_node : out_channel -> v_node -> unit = fun ch n ->
  let prnt = Printf.fprintf in
  match n with
  | VN_Vari(x)     -> prnt ch "VN_Vari(%s)" (name_of x)
  | VN_LAbs(b)     -> prnt ch "VN_LAbs(...)"
  | VN_Cons(c,pv)  -> prnt ch "VN_Cons(%S,%a)" c.elt VPtr.print pv
  | VN_Reco(m)     -> let pelt ch (k, p) = prnt ch "%S=%a" k VPtr.print p in
                      prnt ch "VN_Reco(%a)" (Print.print_map pelt ":") m
  | VN_Scis        -> prnt ch "VN_Scis"
  | VN_VWit(w)     -> prnt ch "VN_VWit(...)"
  | VN_UWit(w)     -> prnt ch "VN_UWit(...)"
  | VN_EWit(w)     -> prnt ch "VN_EWit(...)"

(** Printing function for term nodes. *)
let print_t_node : out_channel -> t_node -> unit = fun ch n ->
  let prnt = Printf.fprintf in
  match n with
  | TN_Vari(a)     -> prnt ch "TN_Vari(%s)" (name_of a)
  | TN_Valu(pv)    -> prnt ch "TN_Valu(%a)" VPtr.print pv
  | TN_Appl(pt,pu) -> prnt ch "TN_Appl(%a,%a)" TPtr.print pt TPtr.print pu
  | TN_MAbs(b)     -> prnt ch "TN_MAbs(...)"
  | TN_Name(s,pt)  -> prnt ch "TN_Name(...)"
  | TN_Proj(pv,l)  -> prnt ch "TN_Proj(%a,%S)" VPtr.print pv  l.elt
  | TN_Case(pv,m)  -> let pelt ch (k, b) = prnt ch "%S → ..." k in
                      let pmap = Print.print_map pelt "|" in
                      prnt ch "TN_Case(%a|%a)" VPtr.print pv pmap m
  | TN_FixY(pt,pv) -> prnt ch "TN_FixY(%a,%a)" TPtr.print pt VPtr.print pv
  | TN_UWit(w)     -> prnt ch "TN_UWit(...)"
  | TN_EWit(w)     -> prnt ch "TN_EWit(...)"

(** Type of a pool. *)
type pool =
  { vs     : v_map
  ; ts     : t_map
  ; next   : int
  ; eq_map : eq_map }

let is_empty : pool -> bool =
  fun {vs; ts} -> VPtrMap.is_empty vs && TPtrMap.is_empty ts

(** Printing a pool (useful for debugging. *)
let print_pool : string -> out_channel -> pool -> unit = fun prefix ch po ->
  if is_empty po then Printf.fprintf ch "%sEMPTY" prefix else
  let {vs ; ts ; eq_map } = po in
  Printf.fprintf ch "%s#### Value nodes ####\n" prefix;
  let fn k (ps, n) =
    Printf.fprintf ch "%s  %a\t→ %a\t← [%a]\n" prefix VPtr.print k
      print_v_node n (Print.print_list Ptr.print ",") ps
  in
  VPtrMap.iter fn vs;
  Printf.fprintf ch "%s#### Term nodes  ####\n" prefix;
  let fn k (ps, n) =
    Printf.fprintf ch "%s  %a\t→ %a\t← [%a]\n" prefix TPtr.print k
      print_t_node n (Print.print_list Ptr.print ",") ps
  in
  TPtrMap.iter fn ts;
  Printf.fprintf ch "%s#### Links       ####\n" prefix;
  let fn p1 p2 =
    Printf.fprintf ch "%s  %a\t→ %a\n" prefix Ptr.print p1 Ptr.print p2
  in
  PtrMap.iter fn eq_map;
  Printf.fprintf ch "%s#####################" prefix

(** Initial, empty pool. *)
let empty_pool : pool =
  { vs     = VPtrMap.empty
  ; ts     = TPtrMap.empty
  ; next   = 0
  ; eq_map = PtrMap.empty }

(** Node search. *)
let find_v_node : VPtr.t -> pool -> Ptr.t list * v_node = fun p po ->
  VPtrMap.find p po.vs

let find_t_node : TPtr.t -> pool -> Ptr.t list * t_node = fun p po ->
  TPtrMap.find p po.ts

(** Equality functions on nodes. *)
let eq_v_nodes : v_node -> v_node -> bool = fun n1 n2 -> n1 == n2 ||
  match (n1, n2) with
  (* FIXME can do better than physical equality on binders / witnesses. *)
  | (VN_Vari(x1)   , VN_Vari(x2)   ) -> eq_variables x1 x2
  | (VN_LAbs(b1)   , VN_LAbs(b2)   ) -> b1 == b2
  | (VN_Cons(c1,p1), VN_Cons(c2,p2)) -> c1.elt = c2.elt && p1 = p2
  | (VN_Reco(m1)   , VN_Reco(m2)   ) -> M.equal (=) m1 m2
  | (VN_Scis       , VN_Scis       ) -> true
  | (VN_VWit(w1)   , VN_VWit(w2)   ) -> let (f1,a1,b1) = w1 in
                                        let (f2,a2,b2) = w2 in
                                        f1 == f2 && a1 == a2 && b1 == b2
  | (VN_UWit(t1,b1), VN_UWit(t2,b2)) -> t1 == t2 && b1 == b2
  | (VN_EWit(t1,b1), VN_EWit(t2,b2)) -> t1 == t2 && b1 == b2
  | (_             , _             ) -> false

let eq_t_nodes : t_node -> t_node -> bool = fun n1 n2 -> n1 == n2 ||
  match (n1, n2) with
  (* FIXME can do better than physical equality on binders / witnesses. *)
  | (TN_Vari(a1)     , TN_Vari(a2)     ) -> eq_variables a1 a2
  | (TN_Valu(p1)     , TN_Valu(p2)     ) -> p1 = p2
  | (TN_Appl(p11,p12), TN_Appl(p21,p22)) -> p11 = p21 && p12 = p22
  | (TN_MAbs(b1)     , TN_MAbs(b2)     ) -> b1 == b2
  | (TN_Name(s1,p1)  , TN_Name(s2,p2)  ) -> s1 == s2 && p1 = p2
  | (TN_Proj(p1,l1)  , TN_Proj(p2,l2)  ) -> p1 = p2 && l1.elt = l2.elt
  | (TN_Case(p1,m1)  , TN_Case(p2,m2)  ) -> p1 = p2 && M.equal (==) m1 m2
  | (TN_FixY(p11,p12), TN_FixY(p21,p22)) -> p11 = p21 && p12 = p22
  | (TN_UWit(t1,b1)  , TN_UWit(t2,b2)  ) -> t1 == t2 && b1 == b2
  | (TN_EWit(t1,b1)  , TN_EWit(t2,b2)  ) -> t1 == t2 && b1 == b2
  | (_               , _               ) -> false

(** Insertion function for nodes. *)
exception FoundV of VPtr.t
let insert_v_node : v_node -> pool -> VPtr.t * pool = fun nn po ->
  let fn p (_,n) = if eq_v_nodes n nn then raise (FoundV p) in
  try VPtrMap.iter fn po.vs; raise Not_found with
  | FoundV(p) -> (p, po)
  | Not_found ->
      let ptr = VPtr.V po.next in
      let vs = VPtrMap.add ptr ([], nn) po.vs in
      let next = po.next + 1 in
      (ptr, { po with vs ; next })

exception FoundT of TPtr.t
let insert_t_node : t_node -> pool -> TPtr.t * pool = fun nn po ->
  let fn p (_,n) = if eq_t_nodes n nn then raise (FoundT p) in
  try TPtrMap.iter fn po.ts; raise Not_found with
  | FoundT(p) -> (p, po)
  | Not_found ->
      let ptr = TPtr.T po.next in
      let ts = TPtrMap.add ptr ([], nn) po.ts in
      let next = po.next + 1 in
      (ptr, { po with ts ; next })

(** Adding a parent to a given node. *)
let add_parent_v_node : VPtr.t -> Ptr.t -> pool -> pool = fun pv pp po ->
  let (ps, n) = find_v_node pv po in
  {po with vs = VPtrMap.add pv (pp::ps, n) po.vs}

let add_parent_t_node : TPtr.t -> Ptr.t -> pool -> pool = fun pt pp po ->
  let (ps, n) = find_t_node pt po in
  {po with ts = TPtrMap.add pt (pp::ps, n) po.ts}

(** Insertion of actual terms and values to the pool. *)
let rec add_term : pool -> term -> TPtr.t * pool = fun po t ->
  match (Norm.whnf t).elt with
  | Vari(a)     -> insert_t_node (TN_Vari(a)) po
  | Valu(v)     -> let (pv, po) = add_valu po v in
                   let (pp, po) = insert_t_node (TN_Valu(pv)) po in
                   let po = add_parent_v_node pv (Ptr.T_ptr pp) po in
                   let eq_map =
                     PtrMap.add (Ptr.T_ptr pp) (Ptr.V_ptr pv) po.eq_map
                   in
                   (pp, {po with eq_map})
  | Appl(t,u)   -> let (pt, po) = add_term po t in
                   let (pu, po) = add_term po u in
                   let (pp, po) = insert_t_node (TN_Appl(pt,pu)) po in
                   let po = add_parent_t_node pt (Ptr.T_ptr pp) po in
                   let po = add_parent_t_node pu (Ptr.T_ptr pp) po in
                   (pp, po)
  | MAbs(_,b)   -> insert_t_node (TN_MAbs(b)) po
  | Name(s,t)   -> let (pt, po) = add_term po t in
                   let (pp, po) = insert_t_node (TN_Name(s,pt)) po in
                   let po = add_parent_t_node pt (Ptr.T_ptr pp) po in
                   (pp, po)
  | Proj(v,l)   -> let (pv, po) = add_valu po v in
                   let (pp, po) = insert_t_node (TN_Proj(pv,l)) po in
                   let po = add_parent_v_node pv (Ptr.T_ptr pp) po in
                   (pp, po)
  | Case(v,m)   -> let (pv, po) = add_valu po v in
                   let m = M.map snd m in
                   let (pp, po) = insert_t_node (TN_Case(pv,m)) po in
                   let po = add_parent_v_node pv (Ptr.T_ptr pp) po in
                   (pp, po)
  | FixY(t,v)   -> let (pt, po) = add_term po t in
                   let (pv, po) = add_valu po v in
                   let (pp, po) = insert_t_node (TN_FixY(pt,pv)) po in
                   let po = add_parent_v_node pv (Ptr.T_ptr pp) po in
                   let po = add_parent_t_node pt (Ptr.T_ptr pp) po in
                   (pp, po)
  | TTyp(t,_)   -> add_term po t
  | TLam(_,b)   -> add_term po (bndr_subst b Dumm)
  | UWit(_,t,b) -> insert_t_node (TN_UWit((t,b))) po
  | EWit(_,t,b) -> insert_t_node (TN_EWit((t,b))) po
  | UVar(_,_)   -> invalid_arg "unification variable in the pool"
  | HApp(_,_,_) -> invalid_arg "higher-order application in the pool"
  | ITag _      -> invalid_arg "integer tags forbidden in the pool"
  | Dumm        -> invalid_arg "dummy terms forbidden in the pool"

and     add_valu : pool -> valu -> VPtr.t * pool = fun po v ->
  match (Norm.whnf v).elt with
  | Vari(x)     -> insert_v_node (VN_Vari(x)) po
  | LAbs(_,b)   -> insert_v_node (VN_LAbs(b)) po
  | Cons(c,v)   -> let (pv, po) = add_valu po v in
                   let (pp, po) = insert_v_node (VN_Cons(c,pv)) po in
                   let po = add_parent_v_node pv (Ptr.V_ptr pp) po in
                   (pp, po)
  | Reco(m)     -> let fn l (_, v) (m, po) =
                     let (pv, po) = add_valu po v in
                     (M.add l pv m, po)
                   in                
                   let (m, po) = M.fold fn m (M.empty, po) in
                   let (pp, po) = insert_v_node (VN_Reco(m)) po in
                   let fn _ pv po = add_parent_v_node pv (Ptr.V_ptr pp) po in
                   let po = M.fold fn m po in
                   (pp, po)
  | Scis        -> insert_v_node VN_Scis po
  | VTyp(v,_)   -> add_valu po v
  | VLam(_,b)   -> add_valu po (bndr_subst b Dumm)
  | VWit(f,a,b) -> insert_v_node (VN_VWit((f,a,b))) po
  | UWit(_,t,b) -> insert_v_node (VN_UWit((t,b))) po
  | EWit(_,t,b) -> insert_v_node (VN_EWit((t,b))) po
  | UVar(_,_)   -> invalid_arg "unification variable in the pool"
  | HApp(_,_,_) -> invalid_arg "higher-order application in the pool"
  | ITag _      -> invalid_arg "integer tags forbidden in the pool"
  | Dumm        -> invalid_arg "dummy terms forbidden in the pool"

(** Recovery of plain term / value. *)
let rec to_term : TPtr.t -> pool -> term = fun p po ->
  let t =
    match snd (find_t_node p po) with
    | TN_Vari(a)     -> Vari(a)
    | TN_Valu(pv)    -> Valu(to_valu pv po)
    | TN_Appl(pt,pu) -> Appl(to_term pt po, to_term pu po)
    | TN_MAbs(b)     -> MAbs(None, b)
    | TN_Name(s,pt)  -> Name(s, to_term pt po)
    | TN_Proj(pv,l)  -> Proj(to_valu pv po, l)
    | TN_Case(pv,m)  -> Case(to_valu pv po, M.map (fun b -> (None, b)) m)
    | TN_FixY(pt,pv) -> FixY(to_term pt po, to_valu pv po)
    | TN_UWit(w)     -> let (t,b) = w in UWit(T,t,b)
    | TN_EWit(w)     -> let (t,b) = w in EWit(T,t,b)
  in Pos.none t

and     to_valu : VPtr.t -> pool -> valu = fun p po ->
  let v =
    match snd (find_v_node p po) with
    | VN_Vari(x)     -> Vari(x)
    | VN_LAbs(b)     -> LAbs(None, b)
    | VN_Cons(c,pv)  -> Cons(c, to_valu pv po)
    | VN_Reco(m)     -> Reco(M.map (fun vp -> (None, to_valu vp po)) m)
    | VN_Scis        -> Scis
    | VN_VWit(w)     -> let (f,a,b) = w in VWit(f,a,b)
    | VN_UWit(w)     -> let (t,b) = w in UWit(V,t,b)
    | VN_EWit(w)     -> let (t,b) = w in EWit(V,t,b)
  in Pos.none v

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

(** Obtain the canonical term / value pointed by a pointer. *)
let rec canonical_term : TPtr.t -> pool -> term * pool = fun p po ->
  let (p, po) = find (Ptr.T_ptr p) po in
  match p with
  | Ptr.T_ptr(p) ->
      let (t, po) =
        match snd (TPtrMap.find p po.ts) with
        | TN_Vari(a)     -> (Vari(a), po)
        | TN_Valu(pv)    -> let (v, po) = canonical_valu pv po in
                            (Valu(v), po)
        | TN_Appl(pt,pu) -> let (t, po) = canonical_term pt po in
                            let (u, po) = canonical_term pu po in
                            (Appl(t,u), po)
        | TN_MAbs(b)     -> (MAbs(None, b), po)
        | TN_Name(s,pt)  -> let (t, po) = canonical_term pt po in
                            (Name(s,t), po)
        | TN_Proj(pv,l)  -> let (v, po) = canonical_valu pv po in
                            (Proj(v,l), po)
        | TN_Case(pv,m)  -> let (v, po) = canonical_valu pv po in
                            (Case(v, M.map (fun b -> (None, b)) m), po)
        | TN_FixY(pt,pv) -> let (t, po) = canonical_term pt po in
                            let (v, po) = canonical_valu pv po in
                            (FixY(t,v), po)
        | TN_UWit(w)     -> (let (t,b) = w in (UWit(T,t,b)), po)
        | TN_EWit(w)     -> (let (t,b) = w in (EWit(T,t,b)), po)
      in (Pos.none t, po)
  | Ptr.V_ptr(p) ->
      let (v, po) = canonical_valu p po in
      (Pos.none (Valu(v)), po)

and     canonical_valu : VPtr.t -> pool -> valu * pool = fun p po ->
  let (p, po) = find (Ptr.V_ptr p) po in
  match p with
  | Ptr.T_ptr(p) -> assert false (* Should never happen. *)
  | Ptr.V_ptr(p) ->
      let (v, po) =
        match snd (VPtrMap.find p po.vs) with
        | VN_Vari(x)     -> (Vari(x), po)
        | VN_LAbs(b)     -> (LAbs(None, b), po)
        | VN_Cons(c,pv)  -> let (v, po) = canonical_valu pv po in
                            (Cons(c,v), po)
        | VN_Reco(m)     -> let fn l pv (m, po) =
                              let (v, po) = canonical_valu pv po in
                              (M.add l (None,v) m, po)
                            in
                            let (m, po) = M.fold fn m (M.empty, po) in
                            (Reco(m), po)
        | VN_Scis        -> (Scis, po)
        | VN_VWit(w)     -> (let (f,a,b) = w in VWit(f,a,b), po)
        | VN_UWit(w)     -> (let (t,b) = w in UWit(V,t,b), po)
        | VN_EWit(w)     -> (let (t,b) = w in EWit(V,t,b), po)
      in (Pos.none v, po)

(** Normalisation function. *)
let rec normalise : TPtr.t -> pool -> Ptr.t * pool = fun p po ->
  let (p, po) = find (Ptr.T_ptr p) po in
  match p with
  | Ptr.V_ptr _  -> (p, po)
  | Ptr.T_ptr pt ->
      begin
        match snd (TPtrMap.find pt po.ts) with
        | TN_Vari(a)     -> (p, po)
        | TN_Valu(pv)    -> find (Ptr.V_ptr pv) po
        | TN_Appl(pt,pu) ->
            begin
              let (pt, po) = find (Ptr.T_ptr pt) po in
              let (pu, po) = find (Ptr.T_ptr pu) po in
              match (pt, pu) with
              | (Ptr.V_ptr pf, Ptr.V_ptr pv) ->
                  begin
                    match snd (VPtrMap.find pf po.vs) with
                    | VN_LAbs(b) ->
                        begin
                          let (v, po) = canonical_valu pv po in
                          let t = bndr_subst b v.elt in
                          let (tp, po) = add_term po t in
                          normalise tp po
                        end
                    | _          -> (p, po)
                  end
              | (_           , _           ) -> (p, po)
            end
        | TN_MAbs(b)     -> (p, po) (* FIXME can do better. *)
        | TN_Name(s,pt)  -> (p, po) (* FIXME can do better. *)
        | TN_Proj(pv,l)  ->
            begin
              let (pv, po) = find_valu pv po in
              match snd (VPtrMap.find pv po.vs) with
              | VN_Reco(m) ->
                  begin
                    try find (Ptr.V_ptr (M.find l.elt m)) po
                    with Not_found -> (p, po)
                  end
              | _          -> (p, po)
            end
        | TN_Case(pv,m)  ->
            begin
              let (pv, po) = find_valu pv po in
              match snd (VPtrMap.find pv po.vs) with
              | VN_Cons(c,pv) ->
                  begin
                    let (pv, po) = find_valu pv po in
                    let (v, po) = canonical_valu pv po in
                    let t = bndr_subst (M.find c.elt m) v.elt in
                    let (tp, po) = add_term po t in
                    normalise tp po
                  end
              | _            -> (p, po)
            end
        | TN_FixY(pt,pv) ->
            begin
              let (t, po) = canonical_term pt po in
              let b = bndr_from_fun "x" (fun x -> FixY(t, Pos.none x)) in
              let (pf, po) = insert_v_node (VN_LAbs(b)) po in
              let (pf, po) = insert_t_node (TN_Valu(pf)) po in
              let (pap, po) = insert_t_node (TN_Appl(pf, pt)) po in
              let (pu, po) = insert_t_node (TN_Valu(pv)) po in
              let (pap, po) = insert_t_node (TN_Appl(pap, pu)) po in
              normalise pap po
            end
        | TN_UWit(w)     -> (p, po)
        | TN_EWit(w)     -> (p, po)
      end

(** Obtain the parents of a pointed node. *)
let parents : Ptr.t -> pool -> Ptr.t list = fun p po ->
  match p with
  | Ptr.V_ptr vp -> fst (find_v_node vp po)
  | Ptr.T_ptr tp -> fst (find_t_node tp po)

(** Union operation. *)
let join : Ptr.t -> Ptr.t -> pool -> pool = fun p1 p2 po ->
  { po with eq_map = PtrMap.add p1 p2 po.eq_map }

let union : Ptr.t -> Ptr.t -> pool -> pool = fun p1 p2 po ->
  let (p1, po) = find p1 po in
  let (p2, po) = find p2 po in
  if p1 = p2 then po else
  match (p1, p2) with
  | (Ptr.T_ptr _  , Ptr.V_ptr _  ) -> join p1 p2 po
  | (Ptr.V_ptr _  , Ptr.T_ptr _  ) -> join p2 p1 po
  | (Ptr.T_ptr _  , Ptr.T_ptr _  ) -> join p1 p2 po (* arbitrary *)
  | (Ptr.V_ptr vp1, Ptr.V_ptr vp2) ->
      begin
        let rec check_equiv vp1 vp2 po =
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
              check_equiv vp1 vp2 po
          (* Records. *)
          | (VN_Reco(m1)    , VN_Reco(m2)    ) ->
              let test vp1 vp2 = check_equiv vp1 vp2 po; true in
              if not (M.equal test m1 m2) then bottom ()
          (* No possible refutation. *)
          | (_              , _              ) -> ()
        in
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
            check_equiv vp1 vp2 po;
            join p1 p2 po (* arbitrary *)
        (* Records. *)
        | (VN_Reco(m1)    , VN_Reco(m2)    ) ->
            let test vp1 vp2 = check_equiv vp1 vp2 po; true in
            if not (M.equal test m1 m2) then bottom ();
            join p1 p2 po (* arbitrary *)
        (* Prefer real values as equivalence class representatives. *)
        | (VN_LAbs(_)     , _              )
        | (VN_Reco(_)     , _              )
        | (VN_Cons(_,_)   , _              ) -> join p2 p1 po
        | (_              , VN_LAbs(_)     )
        | (_              , VN_Reco(_)     )
        | (_              , VN_Cons(_,_)   ) -> join p1 p2 po
        (* Arbitrary join otherwise. *)
        | (_              , _              ) -> join p1 p2 po
      end

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
  log_edp "inserting %a = %a in context\n%a" Print.print_ex t
    Print.print_ex u (print_pool "        ") pool;
  if t == u || eq_expr t u then
    begin
      log_edp "trivial proof";
      {pool}
    end
  else
  let (pt, pool) = add_term pool t in
  let (pu, pool) = add_term pool u in
  let (pt, pool) = normalise pt pool in
  let (pu, pool) = normalise pu pool in
  let pool = union pt pu pool in
  log_edp "obtaining the context\n%a" (print_pool "        ") pool;
  {pool}

(* Adds an inequivalence to a context, producing a bigger context. The
   exception [Contradiction] is raised when expected. *)
let add_inequiv : inequiv -> eq_ctxt -> eq_ctxt = fun (t,u) {pool} ->
  log_edp "inserting %a ≠ %a in context\n%a" Print.print_ex t
    Print.print_ex u (print_pool "        ") pool;
  if t == u || eq_expr t u then
    begin
      log_edp "immediate contradiction";
      raise Contradiction
    end;
  let (pt, pool) = add_term pool t in
  let (pu, pool) = add_term pool u in
  log_edp "after insertion of %a and %a\n%a" TPtr.print pt TPtr.print pu
    (print_pool "        ") pool;
  let (pt, pool) = normalise pt pool in
  let (pu, pool) = normalise pu pool in
  log_edp "after normalisation (%a and %a)\n%a" Ptr.print pt Ptr.print pu
    (print_pool "        ") pool;
  if Ptr.compare pt pu = 0 then
    begin
      log_edp "contradiction found";
      raise Contradiction
    end;
  {pool} (* TODO store clauses *)

(* Main module interface. *)

exception Equiv_error of string
let equiv_error : string -> 'a =
  fun msg -> raise (Equiv_error msg)

(* Test whether a term is equivalent to a value or not. *)
let is_value : term -> eq_ctxt -> bool * eq_ctxt = fun t {pool} ->
  let (pt, pool) = add_term pool t in
  let (pt, pool) = normalise pt pool in
  let res = match pt with Ptr.V_ptr(_) -> true | Ptr.T_ptr(_) -> false in
  log_edp "%a is%s a value" Print.print_ex t (if res then "" else " not");
  (res, {pool})

type relation = term * bool * term (* true means equivalent *)

let learn : eq_ctxt -> relation -> eq_ctxt = fun ctx (t,b,u) ->
  let sym = if b then "=" else "≠" in
  log_edp "learning %a %s %a" Print.print_ex t sym Print.print_ex u;
  try
    let ctx = (if b then add_equiv else add_inequiv) (t,u) ctx in
    log_edp "learned  %a %s %a" Print.print_ex t sym Print.print_ex u;
    ctx
  with Contradiction ->
    log_edp "contradiction in the context";
    raise Contradiction

let prove : eq_ctxt -> relation -> eq_ctxt = fun ctx (t,b,u) ->
  let sym = if b then "=" else "≠" in
  log_edp "proving  %a %s %a in context\n%a" Print.print_ex t sym
    Print.print_ex u (print_pool "        ") ctx.pool;
  try
    ignore ((if b then add_inequiv else add_equiv) (t,u) ctx);
    log_edp "failed to prove %a %s %a" Print.print_ex t sym Print.print_ex u;
    equiv_error "failed to prove an equational relation"
  with Contradiction -> 
    log_edp "proved   %a %s %a" Print.print_ex t sym Print.print_ex u;
    let ctx =
      try learn ctx (t,b,u)
      with Contradiction -> assert false (* unexpected. *)
    in ctx
