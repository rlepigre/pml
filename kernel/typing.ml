(** Main type-checking and subtyping functions. *)

open Bindlib
open Sorts
open Pos
open Ast
open Equiv
open Output
open Compare

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

type ctxt  =
  { uvar_counter : int
  ; equations    : eq_ctxt
  ; positives    : ordi list }

let empty_ctxt =
  { uvar_counter = 0
  ; equations    = empty_ctxt
  ; positives    = [] }

(* New unification variable of the given sort. *)
let new_uvar : type a. ctxt -> a sort -> ctxt * a ex loc = fun ctx s ->
  let i = ctx.uvar_counter in
  let ctx = {ctx with uvar_counter = i+1} in
  log_uni "?%i : %a" i Print.print_sort s;
  (ctx, Pos.none (UVar(s, {uvar_key = i; uvar_val = ref None})))

type typ_rule =
  | Typ_VTyp   of sub_proof * typ_proof
  | Typ_TTyp   of sub_proof * typ_proof
  | Typ_VLam   of typ_proof
  | Typ_TLam   of typ_proof
  | Typ_VWit   of sub_proof
  | Typ_VDef   of value * sub_proof
  | Typ_DSum_i of sub_proof * typ_proof
  | Typ_DSum_e of typ_proof * typ_proof list
  | Typ_Func_i of sub_proof * typ_proof option
  | Typ_Func_e of typ_proof * typ_proof
  | Typ_Func_s of typ_proof * typ_proof
  | Typ_Prod_i of sub_proof * typ_proof list
  | Typ_Prod_e of typ_proof
  | Typ_Name   of typ_proof * stk_proof
  | Typ_Mu     of typ_proof
  | Typ_Scis

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
  | Sub_Exis_r of sub_proof
  | Sub_Univ_r of sub_proof
  | Sub_Exis_l of sub_proof
  | Sub_Rest_l of sub_proof option (* None means contradictory context. *)
  | Sub_Rest_r of sub_proof
  | Sub_Memb_l of sub_proof option (* None means contradictory context. *)
  | Sub_Memb_r of sub_proof
  | Sub_Gene   of sub_proof

and typ_proof = term * prop * typ_rule
and stk_proof = stac * prop * stk_rule
and sub_proof = term * prop * prop * sub_rule

let rec learn_equivalences : ctxt -> valu -> prop -> ctxt = fun ctx wit a ->
  let twit = Pos.none (Valu wit) in
  match (Norm.whnf a).elt with
  | HDef(_,e)  -> learn_equivalences ctx wit e.expr_def
  | Memb(t,a)  -> let equations = learn ctx.equations (twit, true, t) in
                  learn_equivalences {ctx with equations} wit a
  | Rest(a,c)  ->
      begin
        match c with
        | Equiv(eq) -> let equations = learn ctx.equations eq in
                       learn_equivalences {ctx with equations} wit a
        | Posit(_)  -> ctx (* TODO *)
      end
  | Exis(s, f) -> let t = EWit(s,twit,f) in
                  learn_equivalences ctx wit (bndr_subst f t)
  | Prod(fs)   -> ctx (* TODO: wit should be a value
     M.fold (fun lbl p ctxt ->
         learn_equivalences ctxt (Pos.none (Proj(wit,lbl))) p) ctxt fs*)
  | _          -> ctx

let term_is_value : term -> ctxt -> bool * ctxt = fun t ctx ->
  let (is_val, equations) = is_value t ctx.equations in
  (is_val, {ctx with equations})

let rec get_lam : type a. string -> a sort -> term -> prop -> a ex * prop =
  fun x s t c ->
    match (Norm.whnf c).elt with
    | HDef(_,e) -> get_lam x s t e.expr_def
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
    let (t_is_val, ctx) = term_is_value t ctx in
    let (ctx, r) =
      match (a.elt, b.elt) with
      (* Membership on the left. *)
      | (Memb(u,a)  , _          ) when t_is_val ->
          begin
            try
              let equations = learn ctx.equations (t,true,u) in
              let (ctx, p) = subtype {ctx with equations} t a b in
              (ctx, Sub_Memb_l(Some p))
            with Contradiction -> (ctx, Sub_Memb_l(None))
          end
      (* Same types.  *)
      | _ when eq_expr a b         ->
          (ctx, Sub_Equal)
      (* Unfolding of definitions. *)
      | (HDef(_,d)  , _          ) ->
          let (ctx, (_, _, _, r)) = subtype ctx t d.expr_def b in (ctx, r)
      | (_          , HDef(_,d)  ) ->
          let (ctx, (_, _, _, r)) = subtype ctx t a d.expr_def in (ctx, r)
      (* Arrow types. *)
      | (Func(a1,b1), Func(a2,b2)) when t_is_val ->
          let fn x = appl None (box t) (valu None (vari None x)) in
          let f = (None, unbox (vbind mk_free "x" fn)) in
          let wit = Pos.none (Valu(Pos.none (VWit(f,a2,b2)))) in
          let (ctx, p1) = subtype ctx wit a2 a1 in
          let (ctx, p2) = subtype ctx (Pos.none (Appl(t, wit))) b1 b2 in
          (ctx, Sub_Func(p1,p2))
      (* Product (record) types. *)
      | (Prod(fs1)  , Prod(fs2)  ) when t_is_val ->
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
      | (DSum(cs1)  , DSum(cs2)  ) when t_is_val ->
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
      | (_          , Univ(s,f)  ) when t_is_val ->
          let (ctx, p) = subtype ctx t a (bndr_subst f (UWit(s,t,f))) in
          (ctx, Sub_Univ_r(p))
      (* Existential quantification on the left. *)
      | (Exis(s,f)  , _          ) when t_is_val ->
          let (ctx, p) = subtype ctx t (bndr_subst f (EWit(s,t,f))) b in
          (ctx, Sub_Exis_l(p))
      (* Universal quantification on the left. *)
      | (Univ(s,f)  , _          ) ->
          let (ctx, u) = new_uvar ctx s in
          let (ctx, p) = subtype ctx t (bndr_subst f u.elt) b in
          (ctx, Sub_Univ_l(p))
      (* Existential quantification on the right. *)
      | (_          , Exis(s,f)  ) ->
          let (ctx, u) = new_uvar ctx s in
          let (ctx, p) = subtype ctx t a (bndr_subst f u.elt) in
          (ctx, Sub_Exis_r(p))
      (* Membership on the right. *)
      | (_          , Memb(u,b)  ) when t_is_val ->
          let equations = prove ctx.equations (t,true,u) in
          let (ctx, p) = subtype {ctx with equations} t a b in
          (ctx, Sub_Memb_r(p))
      (* Restriction on the left. *)
      | (Rest(a,c)  , _          ) when t_is_val ->
          begin
            match c with
            | Equiv(eq) ->
                begin
                  try
                    let equations = learn ctx.equations eq in
                    let (ctx, p) = subtype {ctx with equations} t a b in
                    (ctx, Sub_Rest_l(Some p))
                  with Contradiction -> (ctx, Sub_Rest_l(None))
                end
            | Posit(o)  ->
                assert false (* TODO *)
          end
      (* Restriction on the right. *)
      | (_          , Rest(b,c)  ) ->
          begin
            match c with
            | Equiv(eq) ->
                let equations = prove ctx.equations eq in
                let (ctx, p) = subtype {ctx with equations} t a b in
                (ctx, Sub_Rest_r(p))
            | Posit(o)  ->
                assert false (* TODO *)
          end
      (* Fallback to general witness. *)
      | (_          , _          ) when not t_is_val ->
          let wit =
            let f = bndr_from_fun "x" (fun x -> Valu(Pos.none x)) in
            Pos.none (Valu(Pos.none (VWit(f, a, b))))
          in
          let (ctx, p) = subtype ctx wit a b in
          (ctx, Sub_Gene(p))
      (* No rule apply. *)
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
        (* Learn the equivalence that are valid in the witness. *)
        begin
          try
            let ctx = learn_equivalences ctx (Pos.none wit) a in
            let (ctx, p2) = type_term ctx (bndr_subst f wit) b in
            (ctx, Typ_Func_i(p1,Some p2))
          with Contradiction -> (ctx, Typ_Func_i(p1, None))
        end
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
          log_typ "Checking case %s." l;
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
    (* Definition. *)
    | HDef(_,d)   ->
        let (ctx, (_, _, r)) = type_valu ctx d.expr_def c in (ctx, r)
    (* Value definition. *)
    | VDef(d)     ->
        let (ctx, p) = subtype ctx t d.value_type c in
        (ctx, Typ_VDef(d,p))
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

    (* Application or strong application. *)
    | Appl(t,u)   ->
       let (is_val, ctx) = term_is_value u ctx in
       let (ctx, a) = new_uvar ctx P in
       let ae = if is_val then Pos.none (Memb(u, a)) else a in
       let (ctx, p2) = type_term ctx u a in
       let (ctx, p1) = type_term ctx t (Pos.none (Func(ae,c))) in
       (ctx, if is_val then Typ_Func_s(p1,p2) else Typ_Func_e(p1,p2))

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
        let check d (p,f) ps =
          log_typ "Checking case %s." d;
          let (_,a) = M.find d ts in
          let wit = Pos.none (VWit(f, a, c)) in
          let t = bndr_subst f wit.elt in
          (try
            let eq =
              let w = Valu (Pos.none (Cons(Pos.none d, wit))) in
              (Pos.none (Valu v), true, Pos.none w)
            in
            let ctx = {ctx with equations = learn ctx.equations eq} in
            let ctx = learn_equivalences ctx wit a in
            (fun () -> snd (type_term ctx t c) :: ps)
          with Contradiction ->
             if not (is_scis t) then
               begin
                 match t.pos with
                 | None   -> Output.wrn_msg "unreachable code..."
                 | Some p -> Output.wrn_msg "unreachable code %a"
                                            Pos.print_short_pos p
               end;
             (fun () -> (t,c,Typ_Scis)::ps)) ()
        in
        let ps = M.fold check m [] in
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
    (* Definition. *)
    | HDef(_,d)   ->
        let (ctx, (_, _, r)) = type_term ctx d.expr_def c in (ctx, r)
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
        let (ctx, p) = subtype ctx wit c a in
        (ctx, Stk_SWit(p))
    (* Definition. *)
    | HDef(_,d)   ->
        let (ctx, (_, _, r)) = type_stac ctx d.expr_def c in (ctx, r)
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
      | HDef(_,_)   -> box e (* NOTE no unification variables in defs. *)
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
      | Rest(a,c)   -> let c =
                         match c with
                         | Equiv(t,b,u) ->
                             equiv (fn sa T uv t x) b (fn sa T uv u x)
                         | Posit(o)     ->
                             posit (fn sa O uv o x)
                       in rest e.pos (fn sa P uv a x) c
      | Impl(c,a)   -> let c =
                         match c with
                         | Equiv(t,b,u) ->
                             equiv (fn sa T uv t x) b (fn sa T uv u x)
                         | Posit(o)     ->
                             posit (fn sa O uv o x)
                       in impl e.pos c (fn sa P uv a x)
      | LAbs(ao,b)  -> labs e.pos (Option.map (fun a -> fn sa P uv a x) ao)
                         (bndr_name b)
                         (fun y -> fn sa T uv (bndr_subst b (mk_free y)) x)
      | Cons(c,v)   -> cons e.pos c (fn sa V uv v x)
      | Reco(m)     -> let gn (l,v) = (l, fn sa V uv v x) in
                       reco e.pos (M.map gn m)
      | Scis        -> scis e.pos
      | VDef(_)     -> box e (* NOTE no unification variables in defs. *)
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
