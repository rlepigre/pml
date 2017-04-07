(** Main type-checking and subtyping functions. *)

open Extra
open Bindlib
open Sorts
open Pos
open Ast
open Equiv
open Output
open Compare

(* Enable circular proofs? *)
let circular = ref false

type sorted = E : 'a sort * 'a ex loc -> sorted

(* Exceptions to be used in case of failure. *)
exception Type_error of sorted * prop * exn
let type_error : sorted -> prop -> exn -> 'a =
  fun t p e -> raise (Type_error(t, p, e))

exception Subtype_msg of pos option * string
let subtype_msg : pos option -> string -> 'a =
  fun pos msg -> raise (Subtype_msg(pos, msg))

exception Subtype_error of term * prop * prop * exn
let subtype_error : term -> prop -> prop -> exn -> 'a =
  fun t a b e -> raise (Subtype_error(t,a,b,e))

exception Bad_schema of string
let bad_schema : string -> 'a =
  fun msg -> raise (Bad_schema(msg))

exception Reachable

exception Unexpected_error of string
let unexpected : string -> 'a =
  fun msg -> raise (Unexpected_error(msg))

(* Log functions registration. *)
let log_sub = Log.register 's' (Some "sub") "subtyping informations"
let log_sub = Log.(log_sub.p)

let log_typ = Log.register 't' (Some "typ") "typing informations"
let log_typ = Log.(log_typ.p)

type ctxt  =
  { uvarcount : int ref
  ; equations : eq_ctxt
  ; positives : ordi list
  ; fix_ihs   : ((v,t) bndr, schema) Buckets.t
  ; top_ih    : Scp.index * ordi array
  ; callgraph : Scp.t }

let empty_ctxt =
  { uvarcount = ref 0
  ; equations = empty_ctxt
  ; positives = []
  ; fix_ihs   = Buckets.empty (==)
  ; top_ih    = (Scp.root, [| |])
  ; callgraph = Scp.create () }

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
  | Typ_Ind    of schema
  | Typ_Goal   of string

and  stk_rule =
  | Stk_Push   of sub_proof * typ_proof * stk_proof
  | Stk_Fram   of typ_proof * stk_proof
  | Stk_SWit   of sub_proof
  | Stk_Goal   of string

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
  | Sub_FixM_r of bool * sub_proof (* boolean true if infinite rule *)
  | Sub_FixN_l of bool * sub_proof (* boolean true if infinite rule *)
  | Sub_FixM_l of bool * sub_proof (* boolean true if infinite rule *)
  | Sub_FixN_r of bool * sub_proof (* boolean true if infinite rule *)

and typ_proof = term * prop * typ_rule
and stk_proof = stac * prop * stk_rule
and sub_proof = term * prop * prop * sub_rule

let learn_nobox : ctxt -> valu -> ctxt = fun ctx v ->
  { ctx with equations =  { pool = add_nobox v ctx.equations.pool } }

(* add to the context some conditions.
   A condition c is added if c false implies wit in a is false.
   as wit may be assumed not box, if c false implies a = Box,
   c can be added *)
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
     A.fold (fun lbl (_, b) ctx ->
         let (v,pool) =  find_proj ctx.equations.pool wit lbl in
         let ctx = { ctx with equations = { pool } } in
         learn_equivalences ctx v b) fs ctx
  | DSum(fs)   ->
     begin
       match find_sum ctx.equations.pool wit with
       | None -> ctx
       | Some(s,v,pool) ->
          try
            let (_, b) = A.find s fs in
            let ctx = { ctx with equations = { pool } } in
            learn_equivalences ctx v b
          with Not_found -> assert false (* NOTE check *)
     end
  | _          -> ctx

let rec is_singleton : prop -> term option = fun t ->
  match (Norm.whnf t).elt with
  | Memb(x,_) -> Some x
  | Rest(t,_) -> is_singleton t
  | _ -> None (* TODO #52: more cases are possible *)

(* add to the context some conditions.
   A condition c is added if c false implies wit in a is true.
   as wit may be assumed not box, if c false implies a = Top,
   c can be added

   The optional argument arg, is given when wit is a lambda.
   in this case, arg is a term such that (wit arg) not in c.
   Therefore, if c = Func(t in a,b) one must have arg t, otherwise
   arg could not be a counter example.
*)
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
    eq_val = (fun v1 v2 ->
      Chrono.add_time equiv_chrono (eq_val ctx.equations v1) v2);
    eq_trm = (fun v1 v2 ->
      Chrono.add_time equiv_chrono (eq_trm ctx.equations v1) v2)
  }

let rec subtype : ctxt -> term -> prop -> prop -> sub_proof =
  fun ctx t a b ->
    log_sub "%a ∈ %a ⊆ %a" Print.ex t Print.ex a Print.ex b;
    let a = Norm.whnf a in
    let b = Norm.whnf b in
    let (t_is_val, ctx) = term_is_value t ctx in
    try let r =
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
         let a2' = (None, unbox (vbind mk_free "x" (fun _ -> box a2))) in
         let vwit = Pos.none (VWit(f,a2',b2)) in
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
              try snd (A.find l fs1) with Not_found ->
              subtype_msg p ("Product clash on label " ^ l ^ "...")
            in
            let t = unbox (t_proj None (box t) (Pos.none l)) in
            let p = subtype ctx t a1 a2 in
            p::ps
          in
          let ps = A.fold check_field fs2 [] in
          Sub_Prod(ps)
      (* Disjoint sum types. *)
      | (DSum(cs1)  , DSum(cs2)  ) when t_is_val ->
          let check_variant c (p,a1) ps =
            let a2 =
              try snd (A.find c cs2) with Not_found ->
              subtype_msg p ("Sum clash on constructor " ^ c ^ "...")
            in
            let t =
              let f x = valu None (vari None x) in
              let id = (None, Pos.none "x", f) in
              unbox (t_case None (box t) (A.singleton c id))
            in
            let p = subtype ctx t a1 a2 in
            p::ps
          in
          let ps = A.fold check_variant cs1 [] in
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
         begin  (* FIXME #42 contradiction poss, if ineq ? *)
            let prf = subtype ctx t a c in
            let _ = prove ctx.equations e in
            Sub_Rest_r(prf)
          end
      (* Implication on the left. *)
      | (Impl(e,c)   , _        ) ->
         begin  (* FIXME #42 contradiction poss, if ineq ? *)
            let prf = subtype ctx t c b in
            let _ = prove ctx.equations e in
            Sub_Rest_r(prf)
          end
      (* Mu right and Nu Left, infinite case. *)
      | (_          , FixM({ elt = Conv },f)) ->
          Sub_FixM_r(true, subtype ctx t a (bndr_subst f b.elt))
      | (FixN({ elt = Conv },f), _) ->
          Sub_FixN_l(true, subtype ctx t (bndr_subst f a.elt) b)
      (* Mu left and Nu right, infinite rules (wrong). *)
      | (FixM({ elt = Conv },f), _          ) when not !circular ->
          Sub_FixM_l(true, subtype ctx t (bndr_subst f a.elt) b)
      | (_          , FixN({ elt = Conv },f)) when not !circular ->
          Sub_FixN_r(true, subtype ctx t a (bndr_subst f b.elt))
      (* Mu right and Nu left rules, general case. *)
      | (_          , FixM(o,f)  ) when !circular ->
          let is_suitable k =
            match (Norm.whnf k).elt with
            | OWMu(m,_,_)
            | OWNu(m,_,_)
            | OSch(m,_,_) -> m == o || Ordinal.less_ordi ctx.positives k o
            | _           -> assert false (* NOTE no others. *)
          in
          let o =
            match List.find_first is_suitable ctx.positives with
            | None   -> subtype_msg b.pos "no suitable ordinal for μr"
            | Some o -> o
          in
          let b = bndr_subst f (FixM(o,f)) in
          Sub_FixM_r(false, subtype ctx t a b)
      | (FixN(o,f)  , _          ) when !circular ->
          let is_suitable k =
            match (Norm.whnf k).elt with
            | OWMu(m,_,_)
            | OWNu(m,_,_)
            | OSch(m,_,_) -> m == o || Ordinal.less_ordi ctx.positives k o
            | _           -> assert false (* NOTE no others. *)
          in
          let o =
            match List.find_first is_suitable ctx.positives with
            | None   -> subtype_msg b.pos "no suitable ordinal for μr"
            | Some o -> o
          in
          let a = bndr_subst f (FixN(o,f)) in
          Sub_FixN_l(false, subtype ctx t a b)
      (* Mu left and Nu right rules. *)
      | (FixM(o,f)  , _          ) when t_is_val && !circular ->
          let ctx = {ctx with positives = o :: ctx.positives} in
          let o =
            let f o = bndr_subst f (FixM(Pos.none o, f)) in
            let f = binder_from_fun "o" f in
            Pos.none (OWMu(o,t,(None,f)))
          in
          let a = bndr_subst f (FixM(o,f)) in
          Sub_FixM_l(false, subtype ctx t a b)
      | (_          , FixN(o,f)  ) when t_is_val && !circular ->
          let ctx = {ctx with positives = o :: ctx.positives} in
          let o =
            let f o = bndr_subst f (FixN(Pos.none o, f)) in
            let f = binder_from_fun "o" f in
            Pos.none (OWNu(o,t,(None, f)))
          in
          let b = bndr_subst f (FixM(o,f)) in
          Sub_FixN_r(false, subtype ctx t a b)
      (* Fallback to general witness. *)
      | (_          , _          ) when not t_is_val ->
         log_sub "general subtyping";
         gen_subtype ctx a b
      (* No rule apply. *)
      | _                          ->
         subtype_msg None "No rule applies"
    in
    (t, a, b, r)
    with
    | Subtype_error _ as e -> raise e
    | e -> subtype_error t a b e

and gen_subtype : ctxt -> prop -> prop -> sub_rule =
  fun ctx a b ->
    let wit =
      let f = bndr_from_fun "x" (fun x -> Valu(Pos.none x)) in
      let a = bndr_from_fun "x" (fun x -> a.elt) in
      Pos.none (Valu(Pos.none (VWit(f, a, b))))
    in
    Sub_Gene(subtype ctx wit a b)

and check_fix : ctxt -> (v, t) bndr -> prop -> typ_proof = fun ctx b c ->
  if not !circular then
    (* Old version. *)
    type_valu ctx (Pos.none (LAbs(None, b))) (Pos.none (Func(c,c)))
  else
  (* Extracting ordinal parameters from the goal type. *)
  let (omb, os) = Misc.bind_ordinals c in
  (* Looking for potential induction hypotheses. *)
  let ihs = Buckets.find b ctx.fix_ihs in
  log_typ "there are %i potential induction hypotheses" (List.length ihs);
  (* Function for finding a suitable induction hypothesis. *)
  let is_suitable ih = eq_ombinder omb (snd ih.sch_judge) in
  match List.find_first is_suitable ihs with
  | Some(ih) ->
      (* An induction hypothesis has been found. *)
      log_typ "an induction hypothesis has been found";
      (* Elimination of the schema, and unification with goal type. *)
      let spe = elim_schema ctx ih in
      let ok = eq_expr (snd spe.spe_judge) c in
      if not ok then bad_schema "cannot unify";
      (* Check positivity of ordinals. *)
      let ok = List.for_all (Ordinal.is_pos ctx.positives) spe.spe_posit in
      if not ok then bad_schema "cannot show positivity";
      (* Add call to call-graph and build the proof. *)
      add_call ctx (ih.sch_index, spe.spe_param) true;
      (build_t_fixy b, c, Typ_Ind(ih))
  | None     ->
      (* No matching induction hypothesis. *)
      log_typ "no suitable induction hypothesis";
      (* Construction of a new schema. *)
      let (sch, os) = generalise ctx b c in
      (* Recording of the new induction hypothesis. *)
      log_typ "the schema has %i arguments" (Array.length os);
      let ctx =
        if os = [||] then ctx
        else { ctx with fix_ihs = Buckets.add b sch ctx.fix_ihs }
      in
      (* Elimination of the schema. *)
      let spe = elim_schema ctx sch in
      let ctx = {ctx with positives = spe.spe_posit} in
      (* Registration of the new top induction hypothesis and call. *)
      let top_ih = (sch.sch_index, os) in
      add_call ctx top_ih false;
      let ctx = {ctx with top_ih } in
      (* Unrolling of the fixpoint and proof continued. *)
      let t = bndr_subst b (build_v_fixy b).elt in
      type_term ctx t (snd spe.spe_judge)

(* Generalisation (construction of a schema). *)
and generalise : ctxt -> (v, t) bndr -> prop -> schema * ordi array =
  fun ctx b c ->
    (* Extracting ordinal parameters from the goal type. *)
    let (omb, os) = Misc.bind_ordinals c in

    let sch_posit = [] in (* FIXME #32 *)
    let sch_relat = [] in (* FIXME #32 *)

    (* Build the judgment. *)
    let sch_judge = (b, omb) in
    (* Ask for a fresh symbol index. *)
    let sch_index =
      let name  = (bndr_name b).elt in
      let names = mbinder_names omb in
      Scp.create_symbol ctx.callgraph name names
    in
    (* Assemble the schema. *)
    ({sch_index ; sch_posit ; sch_relat ; sch_judge}, os)

(* Instantiation of a schema with ordinal unification variables. *)
and elim_schema : ctxt -> schema -> specialised = fun ctx sch ->
  let arity = mbinder_arity (snd sch.sch_judge) in
  let spe_param = Array.init arity (fun _ -> new_uvar ctx O) in
  let xs = Array.map (fun e -> e.elt) spe_param in
  let a = msubst (snd sch.sch_judge) xs in
  let spe_judge = (fst sch.sch_judge, a) in
  let spe_posit = List.map (fun i -> spe_param.(i)) sch.sch_posit in
  { spe_param ; spe_posit ; spe_judge }

(* Add a call to the call-graph. *)
and add_call : ctxt -> (Scp.index * ordi array) -> bool -> unit =
  fun ctx callee is_rec ->
    let caller = ctx.top_ih in
    let matrix = build_matrix ctx.callgraph ctx.positives callee caller in
    let callee = fst callee in
    let caller = fst caller in
    Scp.(add_call ctx.callgraph { callee ; caller ; matrix ; is_rec })

(* Build a call-matrix given the caller and the callee. *)
and build_matrix : Scp.t -> ordi list ->
                     (Scp.index * ordi array) ->
                     (Scp.index * ordi array) ->
                     Scp.matrix = fun calls pos callee caller ->
  let open Scp in
  let w = Scp.arity (fst callee) calls in
  let h = Scp.arity (fst caller) calls in
  let tab = Array.init h (fun _ -> Array.make w Infi) in
  Array.iteri (fun j oj ->
    Array.iteri (fun i oi ->
      assert(j < h); assert(i < w);
      let r =
        if Ordinal.less_ordi pos oi oj then Min1
        else if Ordinal.leq_ordi pos oi oj then Zero
        else Infi
      in
      tab.(j).(i) <- r
    ) (snd callee)) (snd caller);
  { w ; h ; tab }

and type_valu : ctxt -> valu -> prop -> typ_proof = fun ctx v c ->
  let t = Pos.make v.pos (Valu(v)) in
  log_typ "(val) %a : %a" Print.ex v Print.ex c;
  try
  let r =
    match v.elt with
    (* Higher-order application. *)
    | HApp(_,_,_) ->
        begin
          try let (_, _, r) = type_valu ctx (Norm.whnf v) c in r
          with e -> type_error (E(V,v)) c e
        end
    (* λ-abstraction. *)
    | LAbs(ao,f)  ->
       let (x,tx) = unbind mk_free (snd f) in
       begin
         match tx.elt with
         (* Fixpoint. Temporary code *)
         | FixY(b,{elt = Vari y}) ->
            assert(eq_vars x y); (* x must not be free in b *)
            let p = check_fix ctx b c in
            Typ_FixY(p)
         (* General case for typing λ-abstraction *)
         | _                      ->
            let a =
              match ao with
              | None   -> new_uvar ctx P
              | Some a -> a
            in
            let b = new_uvar ctx P in
            let c' = Pos.none (Func(a,b)) in
            let p1 = subtype ctx t c' c in
            let a' = bndr_from_fun (bndr_name f).elt (fun x -> a.elt) in
            let wit = VWit(f, a', b) in
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
    | Cons(d,w)   ->
        let a = new_uvar ctx P in
        let c' = Pos.none (DSum(A.singleton d.elt (None, a))) in
        let p1 = subtype ctx t c' c in
        let ctx = learn_neg_equivalences ctx v None c in
        let p2 = type_valu ctx w a in
        Typ_DSum_i(p1,p2)
    (* Record. *)
    | Reco(m)     ->
        let fn l _ m =
          let a = new_uvar ctx P in
          A.add l (None, a) m
        in
        let pm = A.fold fn m A.empty in
        let c' = Pos.none (Prod(pm)) in
        let p1 = subtype ctx t c' c in
        let ctx = learn_neg_equivalences ctx v None c in
        let fn l (p, v) ps =
          log_typ "Checking case %s." l;
          let (_,a) = A.find l pm in
          let p = type_valu ctx v a in
          p::ps
        in
        let p2s = A.fold fn m [] in
        Typ_Prod_i(p1,p2s)
    (* Scissors. *)
    | Scis        ->
        raise Reachable
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
        let (b, equations) = check_nobox v ctx.equations in
        assert b;
        let p = subtype {ctx with equations} t (bndr_subst a v.elt) c in
        Typ_VWit(p)
    (* Definition. *)
    | HDef(_,d)   ->
        begin
          try let (_, _, r) = type_valu ctx d.expr_def c in r
          with e -> type_error (E(V,v)) c e
        end
    (* Value definition. *)
    | VDef(d)     ->
        let p = subtype ctx t d.value_type c in
        Typ_VDef(d,p)
    (* Goal *)
    | Goal(_,str) ->
        wrn_msg "goal %s %a" str Pos.print_pos_opt v.pos;
        Typ_Goal(str)

    (* Constructors that cannot appear in user-defined terms. *)
    | UWit(_,_,_) -> unexpected "∀-witness during typing..."
    | EWit(_,_,_) -> unexpected "∃-witness during typing..."
    | UVar(_)     -> unexpected "unification variable during typing..."
    | Vari(_)     -> unexpected "Free variable during typing..."
    | Dumm        -> unexpected "Dummy value during typing..."
    | ITag(_)     -> unexpected "ITag during typing..."
  in (Pos.make v.pos (Valu(v)), c, r)
  with
  | Type_error _ as e -> raise e
  | e -> type_error (E(V,v)) c e

and type_term : ctxt -> term -> prop -> typ_proof = fun ctx t c ->
  log_typ "(trm) %a : %a" Print.ex t Print.ex c;
  try
  let r =
    match t.elt with
    (* Higher-order application. *)
    | HApp(_,_,_) ->
        begin
          try let (_, _, r) = type_term ctx (Norm.whnf t) c in r
          with e -> type_error (E(T,t)) c e
        end
    (* Value. *)
    | Valu(v)     ->
        let (_, _, r) = type_valu ctx v c in r
    (* Application or strong application. *)
    | Appl(t,u)   ->
        let a = new_uvar ctx P in
        let (is_val, ctx) = term_is_value u ctx in
        let ae = if is_val then Pos.none (Memb(u, a)) else a in
        let p2 = type_term ctx u a in
        (* NOTE: should learn_equivalences from the type of t, and
           use these equivalences while typing u. Would require to
           type t first and u second which breaks a lot of examples currently.
           Only useful for Scott integer and similar inductive type  *)
        let p1 = type_term ctx t (Pos.none (Func(ae,c))) in
        if is_val then Typ_Func_s(p1,p2) else Typ_Func_e(p1,p2)
    (* μ-abstraction. *)
    | MAbs(b)     ->
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
        let c = Pos.none (Prod(A.singleton l.elt (None, c))) in
        Typ_Prod_e(type_valu ctx v c)
    (* Case analysis. *)
    | Case(v,m)   ->
        let a = new_uvar ctx P in
        let p = type_valu ctx v a in (* infer a type to learn equivalences *)
        let fn d (p,_) m =
          let a = new_uvar ctx P in
          A.add d (p,a) m
        in
        let ts = A.fold fn m A.empty in
        let _p1 = subtype ctx (Pos.none (Valu v)) a (Pos.none (DSum(ts))) in
        let ctx = learn_equivalences ctx v a in
        let check d (p,f) ps =
          log_typ "Checking case %s." d;
          let (_,a) = A.find d ts in
          let eq x =
            let w = Valu (Pos.none (Cons(Pos.none d, Pos.none x))) in
            Equiv(Pos.none (Valu v), true, Pos.none w)
          in
          let fa = bndr_from_fun "x" (fun x -> Rest(a, (eq x))) in
          let wit = Pos.none (VWit(f, fa, c)) in
          let t = bndr_subst f wit.elt in
          (try
            let ctx = learn_nobox ctx wit in
            let ctx = learn_equivalences ctx wit (bndr_subst fa wit.elt) in
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
        let ps = A.fold check m [] in
        Typ_DSum_e(p,List.rev ps)
    (* Coercion. *)
    | TTyp(t,a)   ->
        let p1= subtype ctx t a c in
        let ctx =
          match to_value t ctx.equations with
          | (None, equations)    -> { ctx with equations }
          | (Some(v), equations) ->
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
        begin
          try let (_, _, r) = type_term ctx d.expr_def c in r
          with e -> type_error (E(T,t)) c e
        end
    (* Goal *)
    | Goal(_,str) ->
        wrn_msg "goal %s %a" str Pos.print_pos_opt t.pos;
        Typ_Goal(str)
    (* Constructors that cannot appear in user-defined terms. *)
    | FixY(_,_)   -> unexpected "Fixpoint at the toplevel..."
    | UWit(_,_,_) -> unexpected "∀-witness during typing..."
    | EWit(_,_,_) -> unexpected "∃-witness during typing..."
    | UVar(_)     -> unexpected "unification variable during typing..."
    | Vari(_)     -> unexpected "Free variable during typing..."
    | Dumm        -> unexpected "Dummy value during typing..."
    | ITag(_)     -> unexpected "ITag during typing..."
  in (t, c, r)
  with
  | Type_error _ as e -> raise e
  | e                 -> type_error (E(T,t)) c e

and type_stac : ctxt -> stac -> prop -> stk_proof = fun ctx s c ->
  log_typ "(stk) %a : %a" Print.ex s Print.ex c;
  try
  let r =
    match s.elt with
    (* Higher-order application. *)
    | HApp(_,_,_) ->
        begin
          try let (_, _, r) = type_stac ctx (Norm.whnf s) c in r
          with e -> type_error (E(S,s)) c e
        end
    | Push(v,pi)  ->
        let a = new_uvar ctx P in
        let b = new_uvar ctx P in
        let wit =
          let f = bndr_from_fun "x" (fun x -> Valu(Pos.none x)) in
          let fa = bndr_from_fun "x" (fun x -> a.elt) in
          Pos.none (Valu(Pos.none (VWit(f, fa, b))))
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
          let fa = bndr_from_fun "x" (fun x -> a.elt) in
          Pos.none (Valu(Pos.none (VWit(f, fa, c))))
        in
        Stk_SWit(subtype ctx wit c a)
    (* Definition. *)
    | HDef(_,d)   ->
        begin
          try let (_, _, r) = type_stac ctx d.expr_def c in r
          with e -> type_error (E(S,s)) c e
        end
    (* Goal *)
    | Goal(_,str) ->
        wrn_msg "goal %s at %a" str Pos.print_pos_opt s.pos;
        Stk_Goal(str)
    (* Constructors that cannot appear in user-defined stacks. *)
    | Epsi        -> unexpected "Empty stack during typing..."
    | UWit(_,_,_) -> unexpected "∀-witness during typing..."
    | EWit(_,_,_) -> unexpected "∃-witness during typing..."
    | UVar(_)     -> unexpected "unification variable during typing..."
    | Vari(_)     -> unexpected "Free variable during typing..."
    | Dumm        -> unexpected "Dummy value during typing..."
    | ITag(_)     -> unexpected "Tag during typing..."
  in (s, c, r)
  with
  | Type_error _ as e -> raise e
  | e -> type_error (E(S,s)) c e

let type_check : term -> prop -> prop * typ_proof = fun t a ->
  let ctx = empty_ctxt in
  let prf = type_term ctx t a in
  let l = uvars a in
  assert(l = []); (* FIXME #44 *)
  (Norm.whnf a, prf)

let type_chrono = Chrono.create "typing"

let type_check t = Chrono.add_time type_chrono (type_check t)
