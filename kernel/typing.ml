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
  { uvarcount    : int ref
  ; equations    : eq_ctxt
  ; positives    : ordi list }

let empty_ctxt =
  { uvarcount    = ref 0
  ; equations    = empty_ctxt
  ; positives    = [] }

let new_uvar : type a. ctxt -> a sort -> a ex loc = fun ctx s ->
  let c = ctx.uvarcount in
  let i = !c in incr c;
  log_uni "?%i : %a" i Print.print_sort s;
  Pos.none (UVar(s, {uvar_key = i; uvar_val = ref None}))

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
  | Typ_FixY   of typ_proof

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
  | Sub_FixM_i of sub_proof
  | Sub_FixN_i of sub_proof

and typ_proof = term * prop * typ_rule
and stk_proof = stac * prop * stk_rule
and sub_proof = term * prop * prop * sub_rule

let learn_nobox : ctxt -> valu -> ctxt = fun ctx v ->
  { ctx with equations =  { pool = add_nobox v ctx.equations.pool } }

let rec learn_equivalences : ctxt -> valu -> prop -> ctxt = fun ctx wit a ->
  let twit = Pos.none (Valu wit) in
  match (Norm.whnf a).elt with
  | HDef(_,e)  -> learn_equivalences ctx wit e.expr_def
  | Memb(t,a)  -> let equations = learn ctx.equations (Equiv(twit, true, t)) in
                  learn_equivalences {ctx with equations} wit a
  | Rest(a,c)  -> let equations = learn ctx.equations c in
                  learn_equivalences {ctx with equations} wit a
  | Exis(s, f) -> let t = EWit(s,twit,f) in
                  learn_equivalences ctx wit (bndr_subst f t)
  | Prod(fs)   ->
     M.fold (fun lbl (_, b) ctx ->
         let (v,pool) =  find_proj ctx.equations.pool wit lbl in
         let ctx = { ctx with equations = { pool } } in
         learn_equivalences ctx v b) fs ctx
  | DSum(fs)   ->
     begin
       match find_sum ctx.equations.pool wit with
       | None -> ctx
       | Some(s,v,pool) ->
          try
            let (_, b) = M.find s fs in
            let ctx = { ctx with equations = { pool } } in
            learn_equivalences ctx v b
          with Not_found -> assert false (* NOTE check *)
     end
  | _          -> ctx

let rec is_singleton : prop -> term option = fun t ->
  match (Norm.whnf t).elt with
  | Memb(x,_) -> Some x
  | Rest(t,_) -> is_singleton t
  | _ -> None (* TODO: more cases are possible *)

let rec learn_neg_equivalences : ctxt -> valu -> term option -> prop -> ctxt =
  fun ctx wit arg a ->
    let twit = Pos.none (Valu wit) in
    match (Norm.whnf a).elt, arg with
    | HDef(_,e), _  -> learn_neg_equivalences ctx wit arg e.expr_def
    | Impl(c,a), _  -> let equations = learn ctx.equations c in
                       learn_neg_equivalences {ctx with equations} wit arg a
    | Univ(s, f), _ -> let t = UWit(s,twit,f) in
                       learn_neg_equivalences ctx wit arg (bndr_subst f t)
    | Func(a,b), Some arg ->
       begin
         match is_singleton a with
         | Some x -> let equations = learn ctx.equations (Equiv(arg,true,x)) in
                     {ctx with equations}
         | None -> ctx
       end
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

let oracle ctx = {
    eq_val = (fun v1 v2 -> eq_val ctx.equations v1 v2);
    eq_trm = (fun v1 v2 -> eq_trm ctx.equations v1 v2)
  }

let rec subtype : ctxt -> term -> prop -> prop -> sub_proof =
  fun ctx t a b ->
    log_sub "%a ∈ %a ⊆ %a" Print.ex t Print.ex a Print.ex b;
    let a = Norm.whnf a in
    let b = Norm.whnf b in
    let (t_is_val, ctx) = term_is_value t ctx in
    let r =
      match (a.elt, b.elt) with
      (* Same types.  *)
      | _ when eq_expr ~oracle:(oracle ctx) a b ->
          log_sub "reflexivity applies";
          Sub_Equal
      (* Unfolding of definitions. *)
      | (HDef(_,d)  , _          ) ->
          let (_, _, _, r) = subtype ctx t d.expr_def b in r
      | (_          , HDef(_,d)  ) ->
          let (_, _, _, r) = subtype ctx t a d.expr_def in r
      (* Arrow types. *)
      | (Func(a1,b1), Func(a2,b2)) when t_is_val ->
         let fn x = appl None (box t) (valu None (vari None x)) in
         let f = (None, unbox (vbind mk_free "x" fn)) in
         let vwit = Pos.none (VWit(f,a2,b2)) in
         let ctx = learn_nobox ctx vwit in
         let wit = Pos.none (Valu(vwit)) in
         let ctx, wit = match is_singleton a2 with
           | Some x ->
             let equations = learn ctx.equations (Equiv(x,true,wit)) in
             let ctx = { ctx with equations } in
             (ctx, wit)
           | None ->
              (ctx, wit)
         in
         let p1, p2 =
           match is_singleton a1 with
           | Some _ ->
              let p1 = subtype ctx wit a2 a1 in
              let p2 = subtype ctx (Pos.none (Appl(t, wit))) b1 b2 in
              (p1,p2)
           | None ->
              let p2 = subtype ctx (Pos.none (Appl(t, wit))) b1 b2 in
              let p1 = subtype ctx wit a2 a1 in
              (p1,p2)
          in
          Sub_Func(p1,p2)
      (* Product (record) types. *)
      | (Prod(fs1)  , Prod(fs2)  ) when t_is_val ->
          let check_field l (p,a2) ps =
            let a1 =
              try snd (M.find l fs1) with Not_found ->
              subtype_error p ("Product clash on label " ^ l ^ "...")
            in
            let t = unbox (t_proj None (box t) (Pos.none l)) in
            let p = subtype ctx t a1 a2 in
            p::ps
          in
          let ps = M.fold check_field fs2 [] in
          Sub_Prod(ps)
      (* Disjoint sum types. *)
      | (DSum(cs1)  , DSum(cs2)  ) when t_is_val ->
          let check_variant c (p,a1) ps =
            let a2 =
              try snd (M.find c cs2) with Not_found ->
              subtype_error p ("Sum clash on constructor " ^ c ^ "...")
            in
            let t =
              let f x = valu None (vari None x) in
              let id = (None, Pos.none "x", f) in
              unbox (t_case None (box t) (M.singleton c id))
            in
            let p = subtype ctx t a1 a2 in
            p::ps
          in
          let ps = M.fold check_variant cs1 [] in
          Sub_DSum(ps)
      (* Universal quantification on the right. *)
      | (_          , Univ(s,f)  ) ->
         if t_is_val then
           Sub_Univ_r(subtype ctx t a (bndr_subst f (UWit(s,t,f))))
         else
           gen_subtype ctx a b
      (* Existential quantification on the left. *)
      | (Exis(s,f)  , _          ) ->
         if t_is_val then
           let wit = EWit(s,t,f) in
           Sub_Exis_l(subtype ctx t (bndr_subst f wit) b)
         else
           gen_subtype ctx a b
      (* Universal quantification on the left. *)
      | (Univ(s,f)  , _          ) ->
          let u = new_uvar ctx s in
          Sub_Univ_l(subtype ctx t (bndr_subst f u.elt) b)
      (* Existential quantification on the right. *)
      | (_          , Exis(s,f)  ) ->
          let u = new_uvar ctx s in
          Sub_Exis_r(subtype ctx t a (bndr_subst f u.elt))
      (* Membership on the left. *)
      | (Memb(u,c)  , _          ) ->
         if t_is_val then
           try
             let equations = learn ctx.equations (Equiv(t,true,u)) in
             Sub_Memb_l(Some(subtype {ctx with equations} t c b))
           with Contradiction -> Sub_Memb_l(None)
         (* NOTE may need a backtrack because a right rule could work *)
         else gen_subtype ctx a b
      (* Restriction on the left. *)
      | (Rest(c,e)  , _          ) ->
         if t_is_val then
           begin
             try
               let equations = learn ctx.equations e in
               Sub_Rest_l(Some(subtype {ctx with equations} t c b))
             with Contradiction -> Sub_Rest_l(None)
           end
          (* NOTE may need a backtrack because a right rule could work *)
          else gen_subtype ctx a b
      (* Implication on the right. *)
      | (_          , Impl(e,c)  ) ->
         if t_is_val then
           begin
             try
               let equations = learn ctx.equations e in
               Sub_Rest_l(Some(subtype {ctx with equations} t a c))
             with Contradiction -> Sub_Rest_l(None)
           end
          (* NOTE may need a backtrack because a right rule could work *)
          else gen_subtype ctx a b
      (* Membership on the right. *)
      | (_          , Memb(u,b)  ) when t_is_val ->
          let equations = prove ctx.equations (Equiv(t,true,u)) in
          Sub_Memb_r(subtype {ctx with equations} t a b)
      (* Restriction on the right. *)
      | (_          , Rest(c,e)  ) ->
         begin  (* FIXME: contradiction poss, if ineq ? *)
            let prf = subtype ctx t a c in
            let _ = prove ctx.equations e in
            Sub_Rest_r(prf)
          end
      (* Implication on the left. *)
      | (Impl(e,c)   , _        ) ->
         begin  (* FIXME: contradiction poss, if ineq ? *)
            let prf = subtype ctx t c b in
            let _ = prove ctx.equations e in
            Sub_Rest_r(prf)
          end
      (* Mu, Nu infinite case. *)
      | (_          , FixM({ elt = Conv },f)) ->
         Sub_FixM_i(subtype ctx t a (bndr_subst f b.elt))
      | (FixN({ elt = Conv },f), _) ->
         Sub_FixN_i(subtype ctx t (bndr_subst f a.elt) b)
      (* Mu, Nu tempory wrong rules FIXME . *)
      | (_          , FixN({ elt = Conv },f)) ->
         Sub_FixN_i(subtype ctx t a (bndr_subst f b.elt))
      | (FixM({ elt = Conv },f), _) ->
         Sub_FixM_i(subtype ctx t (bndr_subst f a.elt) b)
      (* Fallback to general witness. *)
      | (_          , _          ) when not t_is_val ->
         log_sub "general subtyping";
         gen_subtype ctx a b
      (* No rule apply. *)
      | _                          ->
          err_msg "cannot show %a ∈ %a ⊆ %a\n%!"
            Print.ex t Print.ex a Print.ex b;
          exit 1
    in
    (t, a, b, r)

and gen_subtype : ctxt -> prop -> prop -> sub_rule =
  fun ctx a b ->
    let wit =
      let f = bndr_from_fun "x" (fun x -> Valu(Pos.none x)) in
      Pos.none (Valu(Pos.none (VWit(f, a, b))))
    in
    Sub_Gene(subtype ctx wit a b)

and type_valu : ctxt -> valu -> prop -> typ_proof = fun ctx v c ->
  let v = Norm.whnf v in
  let t = Pos.make v.pos (Valu(v)) in
  log_typ "(val) %a : %a" Print.ex v Print.ex c;
  let r =
    match v.elt with
    (* λ-abstraction. *)
    | LAbs(ao,f)  ->
       begin
       let (x,tx) = unbind mk_free (snd f) in
         match tx.elt with
         (* Fixpoint. Temporary code *)
         | FixY(t,{ elt = Vari y})   ->
            assert(eq_vars x y);
            (* x must not be free in t *)
            let b = Pos.none (Func(c,c)) in
            let p = type_term ctx t b in
            Typ_FixY(p)
         (* General case for typing λ-abstraction *)
         | _ ->
            let a =
              match ao with
              | None   -> new_uvar ctx P
              | Some a -> a
            in
            let b = new_uvar ctx P in
            let c' = Pos.none (Func(a,b)) in
            (* TODO NuRec ? *)
            let p1 = subtype ctx t c' c in
            let wit = VWit(f, a, b) in
            let twit = Pos.none(Valu (Pos.none wit)) in
            (* Learn the equivalence that are valid in the witness. *)
            begin
              try
                let ctx = learn_nobox ctx (Pos.none wit) in
                let ctx = learn_equivalences ctx (Pos.none wit) a in
                let ctx = learn_neg_equivalences ctx v (Some twit) c in
                let p2 = type_term ctx (bndr_subst f wit) b in
                Typ_Func_i(p1,Some p2)
              with Contradiction -> Typ_Func_i(p1, None)
            end
       end
    (* Constructor. *)
    | Cons(d,v)   ->
        let a = new_uvar ctx P in
        let c' = Pos.none (DSum(M.singleton d.elt (None, a))) in
        (* TODO NuRec ? *)
        let p1 = subtype ctx t c' c in
        let p2 = type_valu ctx v a in
        Typ_DSum_i(p1,p2)
    (* Record. *)
    | Reco(m)     ->
        let fn l _ m =
          let a = new_uvar ctx P in
          M.add l (None, a) m
        in
        let pm = M.fold fn m M.empty in
        let c' = Pos.none (Prod(pm)) in
        (* TODO NuRec ? *)
        let p1 = subtype ctx t c' c in
        let fn l (p, v) ps =
          log_typ "Checking case %s." l;
          let (_,a) = M.find l pm in
          let p = type_valu ctx v a in
          p::ps
        in
        let p2s = M.fold fn m [] in
        Typ_Prod_i(p1,p2s)
    (* Scissors. *)
    | Scis        ->
        type_error v.pos "Reachable scissors..."
    (* Coercion. *)
    | VTyp(v,a)   ->
        let t = Pos.make v.pos (Valu(v)) in
        let p1 = subtype ctx t a c in
        let ctx = learn_neg_equivalences ctx v None c in
        let p2 = type_valu ctx v a in
        Typ_VTyp(p1,p2)
    (* Type abstraction. *)
    | VLam(s,b)   ->
        let (w, c) = get_lam (bndr_name b).elt s t c in
        let p = type_valu ctx (bndr_subst b w) c in
        Typ_VLam(p)
    (* Witness. *)
    | VWit(_,a,_) ->
        let p = subtype ctx t a c in
        Typ_VWit(p)
    (* Definition. *)
    | HDef(_,d)   ->
        let (_, _, r) = type_valu ctx d.expr_def c in r
    (* Value definition. *)
    | VDef(d)     ->
        let p = subtype ctx t d.value_type c in
        Typ_VDef(d,p)
    (* Constructors that cannot appear in user-defined terms. *)
    | UWit(_,_,_) -> unexpected "∀-witness during typing..."
    | EWit(_,_,_) -> unexpected "∃-witness during typing..."
    | UVar(_)     -> unexpected "unification variable during typing..."
    | Vari(_)     -> unexpected "Free variable during typing..."
    | HApp(_)     -> unexpected "Higher-order application during typing..."
    | Dumm        -> unexpected "Dummy value during typing..."
    | ITag(_)     -> unexpected "ITag during typing..."
 in
  (Pos.make v.pos (Valu(v)), c, r)

and type_term : ctxt -> term -> prop -> typ_proof = fun ctx t c ->
  log_typ "(trm) %a : %a" Print.ex t Print.ex c;
  let r =
    match (Norm.whnf t).elt with
    (* Value. *)
    | Valu(v)     ->
       let (_, _, r) = type_valu ctx v c in r

    (* Application or strong application. *)
    | Appl(t,u)   ->
       let a = new_uvar ctx P in
       let (is_val, ctx) = term_is_value u ctx in
       let ae = if is_val then Pos.none (Memb(u, a)) else a in
       let p2 = type_term ctx u a in
       let p1 = type_term ctx t (Pos.none (Func(ae,c))) in
       if is_val then Typ_Func_s(p1,p2) else Typ_Func_e(p1,p2)

    (* μ-abstraction. *)
    | MAbs(b)  ->
        let t = bndr_subst b (SWit(b,c)) in
        Typ_Mu(type_term ctx t c)
    (* Named term. *)
    | Name(pi,t)  ->
        let a = new_uvar ctx P in
        let p1 = type_term ctx t a in
        let p2 = type_stac ctx pi a in
        Typ_Name(p1,p2)
    (* Projection. *)
    | Proj(v,l)   ->
        let c = Pos.none (Prod(M.singleton l.elt (None, c))) in
        Typ_Prod_e(type_valu ctx v c)
    (* Case analysis. *)
    | Case(v,m)   ->
        let fn d (p,_) m =
          let a = new_uvar ctx P in
          M.add d (p,a) m
        in
        let ts = M.fold fn m M.empty in
        let p = type_valu ctx v (Pos.none (DSum(ts))) in
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
            let ctx = {ctx with equations = learn ctx.equations (Equiv(eq))} in
            let ctx = learn_nobox ctx wit in
            let ctx = learn_equivalences ctx wit a in
            (fun () -> type_term ctx t c :: ps)
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
        Typ_DSum_e(p,List.rev ps)
    (* Fixpoint. FIXME temporary code *)
    | FixY(t,v)   ->
       assert false (* FIXME prevent by parsing *)
    (* Coercion. *)
    | TTyp(t,a)   ->
        let p1= subtype ctx t a c in
        let ctx =
          match to_value t ctx.equations with
          | None -> ctx
          | Some(v,equations) ->
             let ctx = { ctx with equations } in
             learn_neg_equivalences ctx v None c
        in
        let p2 = type_term ctx t a in
        Typ_TTyp(p1,p2)
    (* Type abstraction. *)
    | TLam(s,b)   ->
        let (w, c) = get_lam (bndr_name b).elt s t c in
        let p = type_term ctx (bndr_subst b w) c in
        Typ_TLam(p)
    (* Definition. *)
    | HDef(_,d)   ->
        let (_, _, r) = type_term ctx d.expr_def c in r
    (* Constructors that cannot appear in user-defined terms. *)
    | UWit(_,_,_) -> unexpected "∀-witness during typing..."
    | EWit(_,_,_) -> unexpected "∃-witness during typing..."
    | UVar(_)     -> unexpected "unification variable during typing..."
    | Vari(_)     -> unexpected "Free variable during typing..."
    | HApp(_)     -> unexpected "Higher-order application during typing..."
    | Dumm        -> unexpected "Dummy value during typing..."
    | ITag(_)     -> unexpected "ITag during typing..."
  in
  (t, c, r)

and type_stac : ctxt -> stac -> prop -> stk_proof = fun ctx s c ->
  log_typ "(stk) %a : %a" Print.ex s Print.ex c;
  let r =
    match (Norm.whnf s).elt with
    | Push(v,pi)  ->
        let a = new_uvar ctx P in
        let b = new_uvar ctx P in
        let wit =
          let f = bndr_from_fun "x" (fun x -> Valu(Pos.none x)) in
          Pos.none (Valu(Pos.none (VWit(f, a, b))))
        in
        let p1 = subtype ctx wit (Pos.none (Func(a,b))) c in
        let p2 = type_valu ctx v a in
        let p3 = type_stac ctx pi b in
        Stk_Push(p1,p2,p3)
    | Fram(t,pi)  ->
        let a = new_uvar ctx P in
        let p1 = type_term ctx t (Pos.none (Func(c,a))) in
        let p2 = type_stac ctx pi a in
        Stk_Fram(p1,p2)
    | SWit(_,a)   ->
        let wit =
          let f = bndr_from_fun "x" (fun x -> Valu(Pos.none x)) in
          Pos.none (Valu(Pos.none (VWit(f, a, c))))
        in
         Stk_SWit(subtype ctx wit c a)
    (* Definition. *)
    | HDef(_,d)   ->
        let (_, _, r) = type_stac ctx d.expr_def c in r
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
  (s, c, r)

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
                         | NoBox(v)     ->
                             nobox (fn sa V uv v x)
                       in rest e.pos (fn sa P uv a x) c
      | Impl(c,a)   -> let c =
                         match c with
                         | Equiv(t,b,u) ->
                             equiv (fn sa T uv t x) b (fn sa T uv u x)
                         | Posit(o)     ->
                             posit (fn sa O uv o x)
                         | NoBox(v)     ->
                             nobox (fn sa V uv v x)
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
      | MAbs(b)     -> mabs e.pos (bndr_name b)
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
      | OWit(o,i,s) -> owit e.pos (fn sa O uv o x) i (gn sa uv s x)
      | UVar(t,v)   ->
          begin
            match eq_sort sa t with
            | Eq  -> if uvar_eq uv v then box_apply Pos.none x else box e
            | NEq -> box e
          end
  and gn : type a. a sort -> a uvar -> schema -> a ex bindbox
                                            -> schema Bindlib.bindbox =
    fun s uv sch x -> assert false (* FIXME *)
  in
  fun s uv e -> (None, unbox (bind mk_free "X0" (fn s P uv e)))

let type_check : term -> prop option -> prop * typ_proof = fun t ao ->
  let ctx = empty_ctxt in
  let a =
    match ao with
    | None   -> new_uvar ctx P
    | Some a -> a
  in
  let prf = type_term ctx t a in
  let bind_uvar a (U(s,u)) = Pos.none (Univ(s, bind_uvar s u a)) in
  let a = List.fold_left bind_uvar a (uvars a) in
  (Norm.whnf a, prf)

(* FIXME hack to compile the SCP. *)
open Scp
open Ordinal
