(** Equivalence decision procedure. During decision of equivalence, terms are
    stored in a graph (shared among all knonwn terms). Maximal sharing is
    attained by never inserting nodes that are already in the graph. Given
    such a graph (or pool), one will be able to read back the representative
    of a term by following the edges. *)

open Bindlib
open Sorts
open Pos
open Ast

(** Exception raise when the pool contains a contradiction. *)
exception Contradiction
let bottom () = raise Contradiction

(** Module for pointers on a value node of the graph. *)
module VPtr =
  struct
    type t = V of int
    let compare (V i) (V j) = i - j
  end
module VPtrMap = Map.Make(VPtr)

(** Module for pointers on a term node of the graph. *)
module TPtr =
  struct
    type t = T of int
    let compare (T i) (T j) = i - j
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
type v_map = v_node VPtrMap.t

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
type t_map = t_node TPtrMap.t

(** Type of a pool. *)
type pool =
  { vs     : v_map
  ; ts     : t_map
  ; next   : int
  ; eq_map : eq_map }

(** Initial, empty pool. *)
let empty_pool : pool =
  { vs     = VPtrMap.empty
  ; ts     = TPtrMap.empty
  ; next   = 0
  ; eq_map = PtrMap.empty }

(** Node search. *)
let find_v_node : VPtr.t -> pool -> v_node = fun p po ->
  VPtrMap.find p po.vs

let find_t_node : TPtr.t -> pool -> t_node = fun p po ->
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
  | (VN_VWit(w1)   , VN_VWit(w2)   ) -> w1 == w2
  | (VN_UWit(w1)   , VN_UWit(w2)   ) -> w1 == w2
  | (VN_EWit(w1)   , VN_EWit(w2)   ) -> w1 == w2
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
  | (TN_UWit(w1)     , TN_UWit(w2)     ) -> w1 == w2
  | (TN_EWit(w1)     , TN_UWit(w2)     ) -> w1 == w2
  | (_             , _             ) -> false

(** Insertion function for nodes. *)
exception FoundV of VPtr.t
let insert_v_node : v_node -> pool -> VPtr.t * pool = fun nn po ->
  let fn p n = if eq_v_nodes n nn then raise (FoundV p) in
  try VPtrMap.iter fn po.vs; raise Not_found with
  | FoundV(p) -> (p, po)
  | Not_found ->
      let ptr = VPtr.V po.next in
      let vs = VPtrMap.add ptr nn po.vs in
      let next = po.next + 1 in
      (ptr, { po with vs ; next })

exception FoundT of TPtr.t
let insert_t_node : t_node -> pool -> TPtr.t * pool = fun nn po ->
  let fn p n = if eq_t_nodes n nn then raise (FoundT p) in
  try TPtrMap.iter fn po.ts; raise Not_found with
  | FoundT(p) -> (p, po)
  | Not_found ->
      let ptr = TPtr.T po.next in
      let ts = TPtrMap.add ptr nn po.ts in
      let next = po.next + 1 in
      (ptr, { po with ts ; next })

(** Insertion of actual terms and values to the pool. *)
let rec add_term : pool -> term -> TPtr.t * pool = fun po t ->
  match (Norm.whnf t).elt with
  | Vari(a)     -> insert_t_node (TN_Vari(a)) po
  | Valu(v)     -> let (pv, po) = add_valu po v in
                   insert_t_node (TN_Valu(pv)) po
  | Appl(t,u)   -> let (pt, po) = add_term po t in
                   let (pu, po) = add_term po u in
                   insert_t_node (TN_Appl(pt,pu)) po
  | MAbs(_,b)   -> insert_t_node (TN_MAbs(b)) po
  | Name(s,t)   -> let (pt, po) = add_term po t in
                   insert_t_node (TN_Name(s,pt)) po
  | Proj(v,l)   -> let (pv, po) = add_valu po v in
                   insert_t_node (TN_Proj(pv,l)) po
  | Case(v,m)   -> let (pv, po) = add_valu po v in
                   let m = M.map snd m in
                   insert_t_node (TN_Case(pv,m)) po
  | FixY(t,v)   -> let (pt, po) = add_term po t in
                   let (pv, po) = add_valu po v in
                   insert_t_node (TN_FixY(pt,pv)) po
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
                   insert_v_node (VN_Cons(c,pv)) po
  | Reco(m)     -> let fn l (_, v) (m, po) =
                     let (pv, po) = add_valu po v in
                     (M.add l pv m, po)
                   in                
                   let (m, po) = M.fold fn m (M.empty, po) in
                   insert_v_node (VN_Reco(m)) po
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
    match find_t_node p po with
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
    match find_v_node p po with
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
        match TPtrMap.find p po.ts with
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
        match VPtrMap.find p po.vs with
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
        match TPtrMap.find pt po.ts with
        | TN_Vari(a)     -> (p, po)
        | TN_Valu(pv)    -> find (Ptr.V_ptr pv) po
        | TN_Appl(pt,pu) ->
            begin
              let (pt, po) = find (Ptr.T_ptr pt) po in
              let (pu, po) = find (Ptr.T_ptr pu) po in
              match (pt, pu) with
              | (Ptr.V_ptr pf, Ptr.V_ptr pv) ->
                  begin
                    match VPtrMap.find pf po.vs with
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
              match VPtrMap.find pv po.vs with
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
              match VPtrMap.find pv po.vs with
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
          match (VPtrMap.find vp1 po.vs, VPtrMap.find vp2 po.vs) with
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
        match (VPtrMap.find vp1 po.vs, VPtrMap.find vp2 po.vs) with
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

(* Main module interface. *)
type equiv   = term * term
type inequiv = term * term

type eq_ctxt =
  { pool : pool }

let empty_ctxt : eq_ctxt =
  { pool = empty_pool }

(* Adds an equivalence to a context, producing a bigger context. The
   exception [Contradiction] is raised when expected. *)
let add_equiv : equiv -> eq_ctxt -> eq_ctxt = fun (t,u) ctx ->
  if t == u then ctx else
  assert false

(* Adds an inequivalence to a context, producing a bigger context. The
   exception [Contradiction] is raised when expected. *)
let add_inequiv : inequiv -> eq_ctxt -> eq_ctxt = fun (t,u) ctx ->
  if t == u then raise Contradiction else
  assert false

(* Test whether a term is equivalent to a value or not. *)
let is_value : term -> eq_ctxt -> bool = fun t ctx ->
  false (* TODO *)
