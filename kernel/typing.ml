(** Main type-checking and subtyping functions. *)

open Bindlib
open Sorts
open Pos
open Ast
open Equiv
open Output

(* Exceptions to be used in case of failure. *)
exception Type_error of pos option * string
let type_error : pos option -> string -> 'a =
  fun pos msg -> raise (Type_error(pos, msg))

exception Subtype_error of pos option * string
let subtype_error : pos option -> string -> 'a =
  fun pos msg -> raise (Subtype_error(pos, msg))

exception Unexpected_error of string
let unexpected : string -> 'a =
  fun msg -> raise (Unexpected_error(msg))

(* Log functions registration. *)
let log_sub = Log.register 's' (Some "sub") "subtyping informations"
let log_sub = Log.(log_sub.p)

let log_typ = Log.register 't' (Some "typ") "typing informations"
let log_typ = Log.(log_typ.p)

let log_uni = Log.register 'u' (Some "uni") "unification informations"
let log_uni = Log.(log_uni.p)

let log_equ = Log.register 'e' (Some "equ") "equality informations"
let log_equ = Log.(log_equ.p)

type ctxt  =
  { uvar_counter : int
  ; equations    : eq_ctxt }

let empty_ctxt =
  { uvar_counter = 0
  ; equations    = empty_ctxt }

let add_equation : (term * bool * term) -> ctxt -> ctxt = fun (t,eq,u) ctx ->
  let fn = if eq then add_equiv else add_inequiv in
  let equations = fn (t,u) ctx.equations in
  {ctx with equations}

let neg_equation (t,eq,u) = (t, not eq, u)

let new_uvar : type a. ctxt -> a sort -> ctxt * a ex loc = fun ctx s ->
  let i = ctx.uvar_counter in
  let ctx = {ctx with uvar_counter = i+1} in
  log_uni "?%i : %a" i Print.print_sort s;
  (ctx, Pos.none (UVar(s, {uvar_key = i; uvar_val = ref None})))

let uvar_set : type a. a uvar -> a ex loc -> unit = fun u e ->
  log_uni "?%i ← %a" u.uvar_key Print.ex e;
  assert(!(u.uvar_val) = None);
  u.uvar_val := Some e

let uvar_eq : type a. a uvar -> a uvar -> bool =
  fun u v -> u.uvar_key == v.uvar_key

type uvar_fun = { f : 'a. 'a sort -> 'a uvar -> unit }

let rec uvar_iter : type a. uvar_fun -> a ex loc -> unit = fun f e ->
  let uvar_iter_eq f (t,_,u) = uvar_iter f t; uvar_iter f u in
  match (Norm.whnf e).elt with
  | Vari(_)     -> ()
  | HFun(_,_,b) -> uvar_iter f (bndr_subst b Dumm)
  | HApp(_,a,b) -> uvar_iter f a; uvar_iter f b
  | Func(a,b)   -> uvar_iter f a; uvar_iter f b
  | Prod(m)     -> M.iter (fun _ (_,a) -> uvar_iter f a) m
  | DSum(m)     -> M.iter (fun _ (_,a) -> uvar_iter f a) m
  | Univ(_,b)   -> uvar_iter f (bndr_subst b Dumm)
  | Exis(_,b)   -> uvar_iter f (bndr_subst b Dumm)
  | FixM(o,b)   -> uvar_iter f o; uvar_iter f (bndr_subst b Dumm)
  | FixN(o,b)   -> uvar_iter f o; uvar_iter f (bndr_subst b Dumm)
  | Memb(t,a)   -> uvar_iter f t; uvar_iter f a
  | Rest(a,eq)  -> uvar_iter f a; uvar_iter_eq f eq
  (* NOTE type annotation ignored. *)
  | LAbs(_,b)   -> uvar_iter f (bndr_subst b Dumm)
  | Cons(_,v)   -> uvar_iter f v
  | Reco(m)     -> M.iter (fun _ (_,a) -> uvar_iter f a) m
  | Scis        -> ()
  | Valu(v)     -> uvar_iter f v
  | Appl(t,u)   -> uvar_iter f t; uvar_iter f u
  (* NOTE type annotation ignored. *)
  | MAbs(_,b)   -> uvar_iter f (bndr_subst b Dumm)
  | Name(s,t)   -> uvar_iter f s; uvar_iter f t
  | Proj(v,_)   -> uvar_iter f v
  | Case(v,m)   -> let fn _ (_,b) = uvar_iter f (bndr_subst b Dumm) in
                   uvar_iter f v; M.iter fn m
  | FixY(t,v)   -> uvar_iter f t; uvar_iter f v
  | Epsi        -> ()
  | Push(v,s)   -> uvar_iter f v; uvar_iter f s
  | Fram(t,s)   -> uvar_iter f t; uvar_iter f s
  | Conv        -> ()
  | Succ(o)     -> uvar_iter f o
  (* NOTE type annotations ignored. *)
  | VTyp(v,_)   -> uvar_iter f v
  | TTyp(t,_)   -> uvar_iter f t
  | VLam(_,b)   -> uvar_iter f (bndr_subst b Dumm)
  | TLam(_,b)   -> uvar_iter f (bndr_subst b Dumm)
  | ITag(_)     -> ()
  | Dumm        -> ()
  | VWit(b,a,c) -> uvar_iter f (bndr_subst b Dumm);
                   uvar_iter f a; uvar_iter f c
  | SWit(b,a)   -> uvar_iter f (bndr_subst b Dumm); uvar_iter f a
  | UWit(_,t,b) -> uvar_iter f t; uvar_iter f (bndr_subst b Dumm)
  | EWit(_,t,b) -> uvar_iter f t; uvar_iter f (bndr_subst b Dumm)
  | UVar(s,u)   -> f.f s u

type s_elt = U : 'a sort * 'a uvar -> s_elt

let uvars : type a. a ex loc -> s_elt list = fun e ->
  let uvars = ref [] in
  let f s u =
    let p (U(_,v)) = v.uvar_key == u.uvar_key in
    if not (List.exists p !uvars) then uvars := (U(s,u)) :: !uvars
  in
  uvar_iter {f} e; !uvars

let uvar_occurs : type a b. a uvar -> b ex loc -> bool = fun u e ->
  let f _ v = if v.uvar_key == u.uvar_key then raise Exit in
  try uvar_iter {f} e; false with Exit -> true

let eq_expr : type a. a ex loc -> a ex loc -> bool = fun e1 e2 ->
  log_equ "%a = %a" Print.ex e1 Print.ex e2;
  let c = ref (-1) in
  let new_itag : type a. unit -> a ex = fun () -> incr c; ITag(!c) in
  let rec eq_expr : type a. a ex loc -> a ex loc -> bool = fun e1 e2 ->
    match ((Norm.whnf e1).elt, (Norm.whnf e2).elt) with
    | (Vari(x1)      , Vari(x2)      ) ->
        Bindlib.eq_variables x1 x2
    | (HFun(_,_,b1)  , HFun(_,_,b2)  ) ->
        let t = new_itag () in
        eq_expr (bndr_subst b1 t) (bndr_subst b2 t)
    | (HApp(s1,f1,a1), HApp(s2,f2,a2)) ->
        begin
          match eq_sort s1 s2 with
          | Eq  -> eq_expr f1 f2 && eq_expr a1 a2
          | NEq -> false
        end
    | (Func(a1,b1)   , Func(a2,b2)   ) -> eq_expr a1 a2 && eq_expr b1 b2
    | (DSum(m1)      , DSum(m2)      ) ->
        M.equal (fun (_,a1) (_,a2) -> eq_expr a1 a2) m1 m2
    | (Prod(m1)      , Prod(m2)      ) ->
        M.equal (fun (_,a1) (_,a2) -> eq_expr a1 a2) m1 m2
    | (Univ(s1,b1)   , Univ(s2,b2)   ) ->
        begin
          match eq_sort s1 s2 with
          | Eq  -> let t = new_itag () in
                   eq_expr (bndr_subst b1 t) (bndr_subst b2 t)
          | NEq -> false
        end
    | (Exis(s1,b1)   , Exis(s2,b2)   ) ->
        begin
          match eq_sort s1 s2 with
          | Eq  -> let t = new_itag () in
                   eq_expr (bndr_subst b1 t) (bndr_subst b2 t)
          | NEq -> false
        end
    | (FixM(o1,b1)   , FixM(o2,b2)   ) ->
        let t = new_itag () in
        eq_expr o1 o2 && eq_expr (bndr_subst b1 t) (bndr_subst b2 t)
    | (FixN(o1,b1)   , FixN(o2,b2)   ) ->
        let t = new_itag () in
        eq_expr o1 o2 && eq_expr (bndr_subst b1 t) (bndr_subst b2 t)
    | (Memb(t1,a1)   , Memb(t2,a2)   ) -> eq_expr t1 t2 && eq_expr a1 a2
    | (Rest(a1,eq1)  , Rest(a2,eq2)  ) ->
        let (t1,b1,u1) = eq1 and (t2,b2,u2) = eq2 in
        b1 = b2 && eq_expr a1 a2 && eq_expr t1 t2 && eq_expr u1 u2
    (* NOTE type annotation ignored. *)
    | (LAbs(_,b1)    , LAbs(_,b2)    ) ->
        let t = new_itag () in eq_expr (bndr_subst b1 t) (bndr_subst b2 t)
    | (Cons(c1,v1)   , Cons(c2,v2)   ) -> c1.elt = c2.elt && eq_expr v1 v2
    | (Reco(m1)      , Reco(m2)      ) ->
        M.equal (fun (_,v1) (_,v2) -> eq_expr v1 v2) m1 m2
    | (Scis          , Scis          ) -> true
    | (Valu(v1)      , Valu(v2)      ) -> eq_expr v1 v2
    | (Appl(t1,u1)   , Appl(t2,u2)   ) -> eq_expr t1 t2 && eq_expr u1 u2
    (* NOTE type annotation ignored. *)
    | (MAbs(_,b1)    , MAbs(_,b2)    ) ->
        let t = new_itag () in eq_expr (bndr_subst b1 t) (bndr_subst b2 t)
    | (Name(s1,t1)   , Name(s2,t2)   ) -> eq_expr s1 s2 && eq_expr t1 t2
    | (Proj(v1,l1)   , Proj(v2,l2)   ) -> l1.elt = l2.elt && eq_expr v1 v2
    | (Case(v1,m1)   , Case(v2,m2)   ) ->
        let cmp (_,b1) (_,b2) =
          let t = new_itag () in eq_expr (bndr_subst b1 t) (bndr_subst b2 t)
        in
        eq_expr v1 v2 && M.equal cmp m1 m2
    | (FixY(t1,v1)   , FixY(t2,v2)   ) -> eq_expr t1 t2 && eq_expr v1 v2
    | (Epsi          , Epsi          ) -> true
    | (Push(v1,s1)   , Push(v2,s2)   ) -> eq_expr v1 v2 && eq_expr s1 s2
    | (Fram(t1,s1)   , Fram(t2,s2)   ) -> eq_expr t1 t2 && eq_expr s1 s2
    | (Conv          , Conv          ) -> true
    | (Succ(o1)      , Succ(o2)      ) -> eq_expr o1 o2
    (* NOTE type annotations ignored. *)
    | (VTyp(v1,_)    , _             ) -> eq_expr v1 e2
    | (_             , VTyp(v2,_)    ) -> eq_expr e1 v2
    | (TTyp(t1,_)    , _             ) -> eq_expr t1 e2
    | (_             , TTyp(t2,_)    ) -> eq_expr e1 t2
    | (VLam(_,b1)    , _             ) -> eq_expr (bndr_subst b1 Dumm) e2
    | (_             , VLam(_,b2)    ) -> eq_expr e1 (bndr_subst b2 Dumm)
    | (TLam(_,b1)    , _             ) -> eq_expr (bndr_subst b1 Dumm) e2
    | (_             , TLam(_,b2)    ) -> eq_expr e1 (bndr_subst b2 Dumm)
    | (ITag(i1)      , ITag(i2)      ) -> i1 = i2
    (* NOTE should not be compare dummy expressions. *)
    | (Dumm          , Dumm          ) -> false
    | (VWit(f1,a1,b1), VWit(f2,a2,b2)) ->
        let t = new_itag () in
        eq_expr (bndr_subst f1 t) (bndr_subst f2 t) && eq_expr a1 a2 && eq_expr b1 b2
    | (SWit(f1,a1)   , SWit(f2,a2)   ) ->
        let t = new_itag () in
        eq_expr (bndr_subst f1 t) (bndr_subst f2 t) && eq_expr a1 a2
    | (UWit(s1,t1,b1), UWit(s2,t2,b2)) ->
        begin
          match eq_sort s1 s2 with
          | Eq  -> let t = new_itag () in
                   eq_expr (bndr_subst b1 t) (bndr_subst b2 t) && eq_expr t1 t2
          | NEq -> false
        end
    | (EWit(s1,t1,b1), EWit(s2,t2,b2)) ->
        begin
          match eq_sort s1 s2 with
          | Eq  -> let t = new_itag () in
                   eq_expr (bndr_subst b1 t) (bndr_subst b2 t) && eq_expr t1 t2
          | NEq -> false
        end
    | (UVar(_,u1)    , UVar(_,u2)    ) ->
        if u1.uvar_key <> u2.uvar_key then uvar_set u1 e2;
        true
    | (UVar(_,u1)    , _             ) ->
        if uvar_occurs u1 e2 then false else (uvar_set u1 e2; true)
    | (_             , UVar(_,u2)    ) ->
        if uvar_occurs u2 e1 then false else (uvar_set u2 e1; true)
    | _                                -> false
  in eq_expr e1 e2

type typ_rule =
  | Typ_VTyp   of sub_proof * typ_proof
  | Typ_TTyp   of sub_proof * typ_proof
  | Typ_VLam   of typ_proof
  | Typ_TLam   of typ_proof
  | Typ_VWit   of sub_proof
  | Typ_DSum_i of sub_proof * typ_proof
  | Typ_DSum_e of typ_proof * typ_proof list
  | Typ_Func_i of sub_proof * typ_proof
  | Typ_Func_e of typ_proof * typ_proof
  | Typ_Func_s of typ_proof * typ_proof
  | Typ_Prod_i of sub_proof * typ_proof list
  | Typ_Prod_e of typ_proof
  | Typ_Name   of typ_proof * stk_proof
  | Typ_Mu     of typ_proof

and  stk_rule =
  | Stk_Push   of sub_proof * typ_proof * stk_proof
  | Stk_Fram   of typ_proof * stk_proof
  | Stk_SWit   of sub_proof

and  sub_rule =
  | Sub_Equal
  | Sub_Func   of sub_proof * sub_proof
  | Sub_Prod   of sub_proof list
  | Sub_DSum   of sub_proof list
  | Sub_Univ_l of sub_proof
  | Sub_Univ_r of sub_proof
  | Sub_Rest_l of sub_proof
  | Sub_Rest_r of sub_proof
  | Sub_Memb_l of sub_proof
  | Sub_Memb_r of sub_proof

and typ_proof = term * prop * typ_rule
and stk_proof = stac * prop * stk_rule
and sub_proof = term * prop * prop * sub_rule



let rec get_lam : type a. string -> a sort -> term -> prop -> a ex * prop =
  fun x s t c ->
    match (Norm.whnf c).elt with
    | Univ(k,f) when (bndr_name f).elt <> x ->
        unexpected "Name missmatch between Λ and ∀..."
    | Univ(k,f) ->
        begin
          match eq_sort s k with
          | Eq  -> let wit = UWit(k,t,f) in (wit, bndr_subst f wit)
          | NEq -> unexpected "Sort missmatch between Λ and ∀..."
        end
    | _         -> unexpected "Expected ∀ type..."

let rec subtype : ctxt -> term -> prop -> prop -> ctxt * sub_proof =
  fun ctx t a b ->
    log_sub "%a ∈ %a ⊆ %a" Print.ex t Print.ex a Print.ex b;
    let a = Norm.whnf a in
    let b = Norm.whnf b in
    let (ctx, r) =
      match (a.elt, b.elt) with
      (* Same types.  *)
      | _ when eq_expr a b         ->
          (ctx, Sub_Equal)
      (* Arrow types. *)
      | (Func(a1,b1), Func(a2,b2)) ->
          let fn x = appl None (box t) (valu None (vari None x)) in
          let f = (None, unbox (vbind mk_free "x" fn)) in
          let wit = Pos.none (Valu(Pos.none (VWit(f,a2,b2)))) in
          let (ctx, p1) = subtype ctx wit a2 a1 in
          let (ctx, p2) = subtype ctx (Pos.none (Appl(t, wit))) b1 b2 in
          (ctx, Sub_Func(p1,p2))
      (* Product (record) types. *)
      | (Prod(fs1)  , Prod(fs2)  ) ->
          let check_field l (p,a2) (ctx,ps) =
            let a1 =
              try snd (M.find l fs1) with Not_found ->
              subtype_error p ("Product clash on label " ^ l ^ "...")
            in
            let t = unbox (t_proj None (box t) (Pos.none l)) in
            let (ctx, p) = subtype ctx t a1 a2 in
            (ctx, p::ps)
          in
          let (ctx, ps) = M.fold check_field fs2 (ctx,[]) in
          (ctx, Sub_Prod(ps))
      (* Disjoint sum types. *)
      | (DSum(cs1)  , DSum(cs2)  ) ->
          let check_variant c (p,a1) (ctx,ps) =
            let a2 =
              try snd (M.find c cs2) with Not_found ->
              subtype_error p ("Sum clash on constructor " ^ c ^ "...")
            in
            let t =
              let f x = valu None (vari None x) in
              let id = (None, Pos.none "x", f) in
              unbox (t_case None (box t) (M.singleton c id))
            in
            let (ctx, p) = subtype ctx t a1 a2 in
            (ctx, p::ps)
          in
          let (ctx, ps) = M.fold check_variant cs1 (ctx,[]) in
          (ctx, Sub_DSum(ps))
      (* Universal quantification on the right. *)
      | (_          , Univ(s,f)  ) ->
          let (ctx, p) = subtype ctx t a (bndr_subst f (UWit(s,t,f))) in
          (ctx, Sub_Univ_r(p))
      (* Universal quantification on the left. *)
      | (Univ(s,f)  , _          ) ->
          let (ctx, u) = new_uvar ctx s in
          let (ctx, p) = subtype ctx t (bndr_subst f u.elt) b in
          (ctx, Sub_Univ_l(p))
      (* Membership on the left. *)
      | (Memb(u,a)  , _          ) ->
          begin
            try
              let ctx = add_equation (t,true,u) ctx in
              let (ctx, p) = subtype ctx t a b in
              (ctx, Sub_Memb_l(p))
            with Contradiction ->
              assert false (* FIXME Nothing to do, finish the proof. *)
          end
      (* Membership on the right. *)
      | (_          , Memb(u,b)  ) ->
          begin
            try
              let _ = add_equation (t,false,u) ctx in
              assert false (* FIXME error. *)
            with Contradiction ->
              let ctx =
                try add_equation (t,true,u) ctx
                with Contradiction -> assert false (* unexpected. *)
              in
              let (ctx, p) = subtype ctx t a b in
              (ctx, Sub_Memb_r(p))
          end
      (* Restriction on the left. *)
      | (Rest(a,eq) , _          ) ->
          begin
            try
              let ctx = add_equation eq ctx in
              let (ctx, p) = subtype ctx t a b in
              (ctx, Sub_Rest_l(p))
            with Contradiction ->
              assert false (* FIXME Nothing to do, finish the proof. *)
          end
      (* Restriction on the right. *)
      | (_          , Rest(b,eq) ) ->
          begin
            try
              let _ = add_equation (neg_equation eq) ctx in
              assert false (* FIXME error. *)
            with Contradiction ->
              let ctx =
                try add_equation eq ctx
                with Contradiction -> assert false (* unexpected. *)
              in
              let (ctx, p) = subtype ctx t a b in
              (ctx, Sub_Rest_r(p))
          end
      (* TODO *)
      | _                          ->
          err_msg "cannot show %a ∈ %a ⊆ %a\n%!"
            Print.ex t Print.ex a Print.ex b;
          exit 1
    in
    (ctx, (t, a, b, r))

and type_valu : ctxt -> valu -> prop -> ctxt * typ_proof = fun ctx v c ->
  let v = Norm.whnf v in
  let t = build_pos v.pos (Valu(v)) in
  log_typ "(val) %a : %a" Print.ex v Print.ex c;
  let (ctx, r) =
    match v.elt with
    (* λ-abstraction. *)
    | LAbs(ao,f)  ->
        let (ctx, a) =
          match ao with
          | None   -> new_uvar ctx P
          | Some a -> (ctx, a)
        in
        let (ctx, b) = new_uvar ctx P in
        let c' = Pos.none (Func(a,b)) in
        (* TODO NuRec ? *)
        let (ctx, p1) = subtype ctx t c' c in
        let wit = VWit(f, a, b) in
        let (ctx, p2) = type_term ctx (bndr_subst f wit) b in
        (ctx, Typ_Func_i(p1,p2))
    (* Constructor. *)
    | Cons(d,v)   ->
        let (ctx, a) = new_uvar ctx P in
        let c' = Pos.none (DSum(M.singleton d.elt (None, a))) in
        (* TODO NuRec ? *)
        let (ctx, p1) = subtype ctx t c' c in
        let (ctx, p2) = type_valu ctx v a in
        (ctx, Typ_DSum_i(p1,p2))
    (* Record. *)
    | Reco(m)     ->
        let fn l _ (ctx, m) =
          let (ctx,a) = new_uvar ctx P in
          (ctx, M.add l (None, a) m)
        in
        let (ctx, pm) = M.fold fn m (ctx, M.empty) in
        let c' = Pos.none (Prod(pm)) in
        (* TODO NuRec ? *)
        let (ctx, p1) = subtype ctx t c' c in
        let fn l (p, v) (ctx, ps) =
          let (_,a) = M.find l pm in
          let (ctx,p) = type_valu ctx v a in
          (ctx, p::ps)
        in
        let (ctx, p2s) = M.fold fn m (ctx, []) in
        (ctx, Typ_Prod_i(p1,p2s))
    (* Scissors. *)
    | Scis        ->
        type_error v.pos "Reachable scissors..."
    (* Coercion. *)
    | VTyp(v,a)   ->
        let (ctx, p1) = subtype ctx (build_pos v.pos (Valu(v))) a c in
        let (ctx, p2) = type_valu ctx v a in
        (ctx, Typ_VTyp(p1,p2))
    (* Type abstraction. *)
    | VLam(s,b)   ->
        let (w, c) = get_lam (bndr_name b).elt s t c in
        let (ctx, p) = type_valu ctx (bndr_subst b w) c in
        (ctx, Typ_VLam(p))
    (* Witness. *)
    | VWit(_,a,_) ->
        let (ctx, p) = subtype ctx t a c in
        (ctx, Typ_VWit(p))
    (* Constructors that cannot appear in user-defined terms. *)
    | UWit(_,_,_) -> unexpected "∀-witness during typing..."
    | EWit(_,_,_) -> unexpected "∃-witness during typing..."
    | UVar(_)     -> unexpected "unification variable during typing..."
    | Vari(_)     -> unexpected "Free variable during typing..."
    | HApp(_)     -> unexpected "Higher-order application during typing..."
    | Dumm        -> unexpected "Dummy value during typing..."
    | ITag(_)     -> unexpected "Tag during typing..."
  in
  (ctx, (build_pos v.pos (Valu(v)), c, r))

and type_term : ctxt -> term -> prop -> ctxt * typ_proof = fun ctx t c ->
  log_typ "(trm) %a : %a" Print.ex t Print.ex c;
  let (ctx, r) =
    match (Norm.whnf t).elt with
    (* Value. *)
    | Valu(v)     ->
        let (ctx, (_, _, r)) = type_valu ctx v c in (ctx, r)
    (* Strong application. *)
    | Appl(t,u)   when is_value u ctx.equations ->
        let (ctx, a) = new_uvar ctx P in
        let ae = Pos.none (Memb(u, a)) in
        let (ctx, p1) = type_term ctx t (Pos.none (Func(ae,c))) in
        let (ctx, p2) = type_term ctx u a in
        (ctx, Typ_Func_s(p1,p2))
    (* Application. *)
    | Appl(t,u)   ->
        let (ctx, a) = new_uvar ctx P in
        let (ctx, p1) = type_term ctx t (Pos.none (Func(a,c))) in
        let (ctx, p2) = type_term ctx u a in
        (ctx, Typ_Func_e(p1,p2))
    (* μ-abstraction. *)
    | MAbs(ao,b)  ->
        let (ctx, a) =
          match ao with
          | None   -> new_uvar ctx P
          | Some a -> (ctx, a)
        in
        let t = bndr_subst b (SWit(b,c)) in
        let (ctx, p) = type_term ctx t c in
        (ctx, Typ_Mu(p))
    (* Named term. *)
    | Name(pi,t)  ->
        let (ctx, a) = new_uvar ctx P in
        let (ctx, p1) = type_term ctx t a in
        let (ctx, p2) = type_stac ctx pi a in
        (ctx, Typ_Name(p1,p2))
    (* Projection. *)
    | Proj(v,l)   ->
        let c = Pos.none (Prod(M.singleton l.elt (None, c))) in
        let (ctx, p) = type_valu ctx v c in
        (ctx, Typ_Prod_e(p))
    (* Case analysis. *)
    | Case(v,m)   ->
        let fn d (p,_) (m, ctx) =
          let (ctx, a) = new_uvar ctx P in
          (M.add d (p,a) m, ctx)
        in
        let (ts, ctx) = M.fold fn m (M.empty, ctx) in
        let (ctx, p) = type_valu ctx v (Pos.none (DSum(ts))) in
        let check d (p,f) (ctx, ps) =
          let (_,a) = M.find d ts in
          let wit = VWit(f, a, c) in
          let (ctx, p) = type_term ctx (bndr_subst f wit) c in
          (ctx, p::ps)
        in
        let (ctx, ps) = M.fold check m (ctx, []) in
        (ctx, Typ_DSum_e(p,List.rev ps))
    (* Fixpoint. *)
    | FixY(t,v)   ->
        assert false (* TODO *)
    (* Coercion. *)
    | TTyp(t,a)   ->
        let (ctx, p1) = subtype ctx t a c in
        let (ctx, p2) = type_term ctx t a in
        (ctx, Typ_TTyp(p1,p2))
    (* Type abstraction. *)
    | TLam(s,b)   ->
        let (w, c) = get_lam (bndr_name b).elt s t c in
        let (ctx, p) = type_term ctx (bndr_subst b w) c in
        (ctx, Typ_TLam(p))
    (* Constructors that cannot appear in user-defined terms. *)
    | UWit(_,_,_) -> unexpected "∀-witness during typing..."
    | EWit(_,_,_) -> unexpected "∃-witness during typing..."
    | UVar(_)     -> unexpected "unification variable during typing..."
    | Vari(_)     -> unexpected "Free variable during typing..."
    | HApp(_)     -> unexpected "Higher-order application during typing..."
    | Dumm        -> unexpected "Dummy value during typing..."
    | ITag(_)     -> unexpected "Tag during typing..."
  in
  (ctx, (t, c, r))

and type_stac : ctxt -> stac -> prop -> ctxt * stk_proof = fun ctx s c ->
  log_typ "(stk) %a : %a" Print.ex s Print.ex c;
  let (ctx, r) =
    match (Norm.whnf s).elt with
    | Push(v,pi)  ->
        let (ctx, a) = new_uvar ctx P in
        let (ctx, b) = new_uvar ctx P in
        let wit =
          let f = bndr_from_fun "x" (fun x -> Valu(Pos.none x)) in
          Pos.none (Valu(Pos.none (VWit(f, a, b))))
        in
        let (ctx, p1) = subtype ctx wit (Pos.none (Func(a,b))) c in
        let (ctx, p2) = type_valu ctx v a in
        let (ctx, p3) = type_stac ctx pi b in
        (ctx, Stk_Push(p1,p2,p3))
    | Fram(t,pi)  ->
        let (ctx, a) = new_uvar ctx P in
        let (ctx, p1) = type_term ctx t (Pos.none (Func(c,a))) in
        let (ctx, p2) = type_stac ctx pi a in
        (ctx, Stk_Fram(p1,p2))
    | SWit(_,a)   ->
        let wit =
          let f = bndr_from_fun "x" (fun x -> Valu(Pos.none x)) in
          Pos.none (Valu(Pos.none (VWit(f, a, c))))
        in
        let (ctx, p) = subtype ctx wit a c in
        (ctx, Stk_SWit(p))
    (* Constructors that cannot appear in user-defined stacks. *)
    | Epsi        -> unexpected "Empty stack during typing..."
    | UWit(_,_,_) -> unexpected "∀-witness during typing..."
    | EWit(_,_,_) -> unexpected "∃-witness during typing..."
    | UVar(_)     -> unexpected "unification variable during typing..."
    | Vari(_)     -> unexpected "Free variable during typing..."
    | HApp(_)     -> unexpected "Higher-order application during typing..."
    | Dumm        -> unexpected "Dummy value during typing..."
    | ITag(_)     -> unexpected "Tag during typing..."
  in
  (ctx, (s, c, r))

let bind_uvar : type a. a sort -> a uvar -> prop -> (a, p) bndr =
  let rec fn : type a b. a sort -> b sort -> a uvar -> b ex loc
               -> a ex bindbox -> b box =
    fun sa sb uv e x ->
      let e = Norm.whnf e in
      match e.elt with
      | Vari(x)     -> vari None x
      | HFun(s,t,b) -> hfun e.pos s t (bndr_name b)
                         (fun y -> fn sa t uv (bndr_subst b (mk_free y)) x)
      | HApp(s,a,b) -> happ e.pos s (fn sa (F(s,sb)) uv a x) (fn sa s uv b x)
      | Func(a,b)   -> func e.pos (fn sa P uv a x) (fn sa P uv b x)
      | Prod(m)     -> let gn (l,a) = (l, fn sa P uv a x) in
                       prod e.pos (M.map gn m)
      | DSum(m)     -> let gn (c,a) = (c, fn sa P uv a x) in
                       dsum e.pos (M.map gn m)
      | Univ(s,b)   -> univ e.pos (bndr_name b) s
                         (fun y -> fn sa sb uv (bndr_subst b (mk_free y)) x)
      | Exis(s,b)   -> exis e.pos (bndr_name b) s
                         (fun y -> fn sa sb uv (bndr_subst b (mk_free y)) x)
      | FixM(o,b)   -> fixm e.pos (fn sa O uv o x) (bndr_name b)
                         (fun y -> fn sa P uv (bndr_subst b (mk_free y)) x)
      | FixN(o,b)   -> fixm e.pos (fn sa O uv o x) (bndr_name b)
                         (fun y -> fn sa P uv (bndr_subst b (mk_free y)) x)
      | Memb(t,a)   -> memb e.pos (fn sa T uv t x) (fn sa P uv a x)
      | Rest(a,eq)  -> let (t,b,u) = eq in
                       rest e.pos (fn sa P uv a x)
                         ((fn sa T uv t x, b, fn sa T uv u x))
      | LAbs(ao,b)  -> labs e.pos (Option.map (fun a -> fn sa P uv a x) ao)
                         (bndr_name b)
                         (fun y -> fn sa T uv (bndr_subst b (mk_free y)) x)
      | Cons(c,v)   -> cons e.pos c (fn sa V uv v x)
      | Reco(m)     -> let gn (l,v) = (l, fn sa V uv v x) in
                       reco e.pos (M.map gn m)
      | Scis        -> scis e.pos
      | Valu(v)     -> valu e.pos (fn sa V uv v x)
      | Appl(t,u)   -> appl e.pos (fn sa T uv t x) (fn sa T uv u x)
      | MAbs(ao,b)  -> mabs e.pos (Option.map (fun a -> fn sa P uv a x) ao)
                         (bndr_name b)
                         (fun y -> fn sa T uv (bndr_subst b (mk_free y)) x)
      | Name(s,t)   -> name e.pos (fn sa S uv s x) (fn sa T uv t x)
      | Proj(v,l)   -> proj e.pos (fn sa V uv v x) l
      | Case(v,m)   -> let gn (p,b) =
                         let f y = fn sa T uv (bndr_subst b (mk_free y)) x in
                         (p, bndr_name b, f)
                       in
                       case e.pos (fn sa V uv v x) (M.map gn m)
      | FixY(t,v)   -> fixy e.pos (fn sa T uv t x) (fn sa V uv v x)
      | Epsi        -> box e
      | Push(v,s)   -> push e.pos (fn sa V uv v x) (fn sa S uv s x)
      | Fram(t,s)   -> fram e.pos (fn sa T uv t x) (fn sa S uv s x)
      | Conv        -> box e
      | Succ(o)     -> succ e.pos (fn sa O uv o x)
      | VTyp(v,a)   -> vtyp e.pos (fn sa V uv v x) (fn sa P uv a x)
      | TTyp(t,a)   -> ttyp e.pos (fn sa T uv t x) (fn sa P uv a x)
      | VLam(s,b)   -> vlam e.pos (bndr_name b) s
                         (fun y -> fn sa V uv (bndr_subst b (mk_free y)) x)
      | TLam(s,b)   -> tlam e.pos (bndr_name b) s
                         (fun y -> fn sa T uv (bndr_subst b (mk_free y)) x)
      | ITag(_)     -> box e
      | Dumm        -> box e
      | VWit(b,a,c) -> vwit e.pos (bndr_name b)
                         (fun y -> fn sa T uv (bndr_subst b (mk_free y)) x)
                         (fn sa P uv a x) (fn sa P uv c x)
      | SWit(b,a)   -> swit e.pos (bndr_name b)
                         (fun y -> fn sa T uv (bndr_subst b (mk_free y)) x)
                         (fn sa P uv a x)
      | UWit(s,t,b) -> uwit e.pos (fn sa T uv t x) (bndr_name b) s
                         (fun y -> fn sa P uv (bndr_subst b (mk_free y)) x)
      | EWit(s,t,b) -> ewit e.pos (fn sa T uv t x) (bndr_name b) s
                         (fun y -> fn sa P uv (bndr_subst b (mk_free y)) x)
      | UVar(t,v)   ->
          begin
            match eq_sort sa t with
            | Eq  -> if uvar_eq uv v then box_apply Pos.none x else box e
            | NEq -> box e
          end
  in
  fun s uv e -> (None, unbox (bind mk_free "X0" (fn s P uv e)))

let type_check : term -> prop option -> prop * typ_proof = fun t ao ->
  let ctx = empty_ctxt in
  let (ctx, a) =
    match ao with
    | None   -> new_uvar ctx P
    | Some a -> (ctx, a)
  in
  let (ctx, prf) = type_term ctx t a in
  let bind_uvar a (U(s,u)) = Pos.none (Univ(s, bind_uvar s u a)) in
  let a = List.fold_left bind_uvar a (uvars a) in
  (Norm.whnf a, prf)
