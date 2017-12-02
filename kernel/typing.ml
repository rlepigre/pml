(** Main type-checking and subtyping functions. *)

open Extra
open Bindlib
open Sorts
open Pos
open Ast
open Epsilon
open Equiv
open Output
open Uvars
open Compare

type sorted = E : 'a sort * 'a ex loc -> sorted

(* Exceptions to be used in case of failure. *)
exception Type_error of sorted * prop * exn
let type_error : sorted -> prop -> exn -> 'a =
  fun t p e ->
    match e with
    | Out_of_memory -> raise e
    | _             -> raise (Type_error(t, p, e))

exception Subtype_msg of pos option * string
let subtype_msg : pos option -> string -> 'a =
  fun pos msg -> raise (Subtype_msg(pos, msg))

exception Subtype_error of term * prop * prop * exn
let subtype_error : term -> prop -> prop -> exn -> 'a =
  fun t a b e ->
    match e with
    | Out_of_memory -> raise e
    | _             -> raise (Subtype_error(t,a,b,e))

exception Cannot_unify of prop * prop
let cannot_unify : prop -> prop -> 'a =
  fun a b -> raise (Cannot_unify(a,b))

exception Loops of term
let loops : term -> 'a =
  fun t -> raise (Loops(t))

exception Reachable

exception No_typing_IH of strloc

exception Not_total

exception Unexpected_error of string
let unexpected : string -> 'a =
  fun msg -> raise (Unexpected_error(msg))

(* Log functions registration. *)
let log_sub = Log.register 's' (Some "sub") "subtyping informations"
let log_sub = Log.(log_sub.p)

let log_typ = Log.register 't' (Some "typ") "typing informations"
let log_typ = Log.(log_typ.p)

let log_aut = Log.register 'a' (Some "aut") "automatic proving informations"
let log_aut = Log.(log_aut.p)

(* Context. *)
type ctxt  =
  { uvarcount : int ref
  ; equations : eq_ctxt
  ; ctx_names : Bindlib.ctxt
  (* the first of the pair is positive, the second
     is stricly less than the first *)
  ; positives : (ordi * ordi) list
  ; fix_ihs   : ((t,v) bndr, fix_schema) Buckets.t
  ; sub_ihs   : sub_schema list
  ; top_ih    : Scp.index * ordi array
  ; add_calls : (unit -> unit) list ref
  ; auto_lvl  : int * int
  ; in_auto   : bool
  ; callgraph : Scp.t
  ; totality  : Totality.tot }

let default_auto_lvl = ref (0, 100)

let empty_ctxt () =
  { uvarcount = ref 0
  ; equations = empty_ctxt
  ; ctx_names = Bindlib.empty_ctxt
  ; positives = []
  ; fix_ihs   = Buckets.empty (==)
  ; sub_ihs   = []
  ; top_ih    = (Scp.root, [| |])
  ; add_calls = ref []
  ; auto_lvl  = !default_auto_lvl
  ; in_auto   = false
  ; callgraph = Scp.create ()
  ; totality  = Totality.Ter }

let new_uvar : type a. ctxt -> a sort -> a ex loc = fun ctx s ->
  let c = ctx.uvarcount in
  let i = !c in incr c;
  log_uni "?%i : %a" i Print.sort s;
  Pos.none (UVar(s, { uvar_key = i
                    ; uvar_val = ref (Unset [])
                    ; uvar_pur = ref false}))

let add_positive : ctxt -> ordi -> ordi -> ctxt = fun ctx o oo ->
  let o = Norm.whnf o in
  match o.elt with
  | Conv    -> ctx
  | Succ(_) -> ctx
  | _       -> {ctx with positives = (o,oo) :: ctx.positives}

(* Instantation of heterogenous binder with uvars. *)
let rec instantiate : type a b. ctxt -> (a, b) bseq -> b =
  fun ctx seq ->
    match seq with
    | BLast(s,f) -> let u = new_uvar ctx s in
                    subst f u.elt
    | BMore(s,f) -> let u = new_uvar ctx s in
                    instantiate ctx (subst f u.elt)

let extract_vwit_type : valu -> prop = fun v ->
  match (Norm.whnf v).elt with
  | VWit{valu={contents = (_,a,_)}} -> a
  | _                  -> assert false (* should not happen *)

let extract_swit_type : stac -> prop = fun s ->
  match (Norm.whnf s).elt with
  | SWit{valu={contents=(_,a)}} -> a
  | _               -> assert false (* should not happen *)

type typ_rule =
  | Typ_VTyp   of sub_proof * typ_proof
  | Typ_TTyp   of sub_proof * typ_proof
  | Typ_TSuch  of typ_proof
  | Typ_VSuch  of typ_proof
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
  | Typ_Ind    of fix_schema * sub_proof
  | Typ_Goal   of string
  | Typ_Prnt   of sub_proof
  | Typ_Repl   of typ_proof * typ_proof
  | Typ_Delm   of typ_proof

and  stk_rule =
  | Stk_Push   of sub_rule * typ_proof * stk_proof
  | Stk_Fram   of typ_proof * stk_proof
  | Stk_SWit   of sub_rule
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
  | Sub_Rest_r of sub_proof option
  | Sub_Impl_l of sub_proof option (* None means contradictory context. *)
  | Sub_Impl_r of sub_proof option
  | Sub_Memb_l of sub_proof option (* None means contradictory context. *)
  | Sub_Memb_r of sub_proof
  | Sub_Gene   of sub_proof
  | Sub_FixM_r of bool * sub_proof (* boolean true if infinite rule *)
  | Sub_FixN_l of bool * sub_proof (* boolean true if infinite rule *)
  | Sub_FixM_l of bool * sub_proof (* boolean true if infinite rule *)
  | Sub_FixN_r of bool * sub_proof (* boolean true if infinite rule *)
  | Sub_Ind    of sub_schema

and typ_proof = term * prop * typ_rule
and stk_proof = stac * prop * stk_rule
and sub_proof = term * prop * prop * sub_rule

let learn_nobox : ctxt -> valu -> ctxt = fun ctx v ->
  { ctx with equations =  { pool = add_nobox v ctx.equations.pool } }

(* Add to the context some conditions.
   A condition c is added if c false implies wit in a is false.
   as wit may be assumed not box, if c false implies a = Box,
   c can be added *)
let rec learn_equivalences : ctxt -> valu -> prop -> ctxt = fun ctx wit a ->
  let twit = Pos.none (Valu wit) in
  match (Norm.whnf a).elt with
  | HDef(_,e)  -> learn_equivalences ctx wit e.expr_def
  | Memb(t,a)  -> let equations = learn ctx.equations (Equiv(twit,true,t)) in
                  learn_equivalences {ctx with equations} wit a
  | Rest(a,c)  -> let equations = learn ctx.equations c in
                  learn_equivalences {ctx with equations} wit a
  | Exis(s, f) -> let (t, ctx_names) = ewit ctx.ctx_names s twit f in
                  let ctx = { ctx with ctx_names } in
                  learn_equivalences ctx wit (bndr_subst f t.elt)
  | Prod(fs)   ->
     A.fold (fun lbl (_, b) ctx ->
         let (v,pool,ctx_names) =
           find_proj ctx.equations.pool ctx.ctx_names wit lbl
         in
         let ctx = { ctx with equations = { pool }; ctx_names } in
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
  (** Learn positivity of the ordinal *)
  | FixM(o,f)  ->
      let (bound, ctx) =
        match (Norm.whnf o).elt with
        | Succ(o) -> (o, ctx)
        | _       ->
           (** We know that o is positive and wit in a
               so we can build an eps < o *)
           let f o = bndr_subst f (FixM(Pos.none o, f)) in
           let f = binder_from_fun "o" f in
           let (o', ctx_names) = owmu ctx.ctx_names o twit (None, f) in
           (o', { ctx with ctx_names })
      in
      let ctx = add_positive ctx o bound in
      (* NOTE: may loop on mu X.X *)
      learn_equivalences ctx wit (bndr_subst f (FixM(bound,f)))
  | _          -> ctx

let rec is_singleton : prop -> term option = fun t ->
  match (Norm.whnf t).elt with
  | Memb(x,_) -> Some x
  | Rest(t,_) -> is_singleton t
  | _         -> None (* TODO #10: more cases are possible *)

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
    | Univ(s, f), _ -> let (t, ctx_names) = uwit ctx.ctx_names s twit f in
                       let ctx = { ctx with ctx_names } in
                       learn_neg_equivalences ctx wit arg (bndr_subst f t.elt)
    | Func(t,a,b), Some arg ->
       begin
         match is_singleton a with
         | Some x -> let equations = learn ctx.equations (Equiv(arg,true,x)) in
                     {ctx with equations}
         | None -> ctx
       end
  (** Learn positivity of the ordinal *)
    | FixN(o,f), _ ->
      let (bound, ctx) =
        match (Norm.whnf o).elt with
        | Succ(o) -> (o, ctx)
        | _       ->
           (** We know that o is positive and wit in a
               so we can build an eps < o *)
           let f o = bndr_subst f (FixN(Pos.none o, f)) in
           let f = binder_from_fun "o" f in
           let (o', ctx_names) = ownu ctx.ctx_names o twit (None, f) in
           (o', { ctx with ctx_names })
      in
      let ctx = add_positive ctx o bound in
      (* NOTE: may loop on nu X.X *)
      learn_neg_equivalences ctx wit arg (bndr_subst f (FixN(bound,f)))
    | _          -> ctx

let term_is_value : term -> ctxt -> bool * bool * ctxt = fun t ctx ->
  let (is_val, no_box, equations) = is_value t ctx.equations in
  (is_val, no_box, {ctx with equations})

let print_pos : out_channel -> (ordi * ordi) list -> unit =
  fun ch os ->
    match os with
    | [] -> output_string ch "∅"
    | os -> let print ch (o, oo) =
              Printf.fprintf ch "%a (> %a)" Print.ex o Print.ex oo
            in print_list print ", " ch os

let is_conv : ordi -> bool = fun o ->
  match (Norm.whnf o).elt with
  | Conv -> true
  | _    -> false

let type_chrono = Chrono.create "typing"
let sub_chrono = Chrono.create "subtyping"
let check_fix_chrono = Chrono.create "chkfix"
let check_sub_chrono = Chrono.create "chksub"

type check_sub =
  | Sub_Applies of sub_rule
  | Sub_New of ctxt * (prop * prop)

let rec unif_expr : type a. ctxt -> a ex loc -> a ex loc -> bool =
  fun ctx a b ->
    eq_expr ~oracle:(oracle (ref ctx.equations.pool)) ~strict:false a b

and subtype =
  let rec subtype : ctxt -> term -> prop -> prop -> sub_proof =
    fun ctx t a b ->
    log_sub "proving the subtyping judgment:";
    log_sub "  %a\n  ⊢ %a\n  ∈ %a\n  ⊆ %a"
      print_pos ctx.positives Print.ex t Print.ex a Print.ex b;
    let a = Norm.whnf a in
    let b = Norm.whnf b in
    let (t_is_val, _, ctx) = term_is_value t ctx in
    try let r =
      (* Same types.  *)
      if unif_expr ctx a b then
        begin
          log_sub "reflexivity applies";
          Sub_Equal
        end
      else (
      log_sub "reflexivity does not applies";
      match (a.elt, b.elt) with
      (* Unfolding of definitions. *)
      | (HDef(_,d)  , _          ) ->
          let (_, _, _, r) = subtype ctx t d.expr_def b in r
      | (_          , HDef(_,d)  ) ->
          let (_, _, _, r) = subtype ctx t a d.expr_def in r
      (* Universal quantification on the right. *)
      | (_          , Univ(s,f)  ) ->
         if t_is_val then
           let (eps, ctx_names) = uwit ctx.ctx_names s t f in
           let ctx = { ctx with ctx_names } in
           Sub_Univ_r(subtype ctx t a (bndr_subst f eps.elt))
         else
           gen_subtype ctx a b
      (* Existential quantification on the left. *)
      | (Exis(s,f)  , _          ) ->
         if t_is_val then
           let (eps, ctx_names) = ewit ctx.ctx_names s t f in
           let ctx = { ctx with ctx_names } in
           Sub_Exis_l(subtype ctx t (bndr_subst f eps.elt) b)
         else
           gen_subtype ctx a b
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
               Sub_Impl_r(Some(subtype {ctx with equations} t a c))
             with Contradiction -> Sub_Rest_l(None)
           end
          (* NOTE may need a backtrack because a right rule could work *)
          else gen_subtype ctx a b
      (* Mu left and Nu right rules. *)
      | (FixM(o,f)  , _          ) when t_is_val ->
          begin (* heuristic to instanciate some unification variables *)
            match b.elt with
            | FixM(ol,f) ->
               begin
                 match (Norm.whnf ol).elt with
                 | UVar(O,v) -> uvar_set v o
                 | _ -> ()
               end
            | _ -> ()
          end;
          let ctx, o' =
            let o = Norm.whnf o in
            match o.elt with
              Succ o' -> (ctx, o')
            | _ ->
               let f o = bndr_subst f (FixM(Pos.none o, f)) in
               let f = binder_from_fun "o" f in
               let (o', ctx_names) = owmu ctx.ctx_names o t (None,f) in
               let ctx = { ctx with ctx_names } in
               (add_positive ctx o o', o')
          in
          let a = bndr_subst f (FixM(o',f)) in
          Sub_FixM_l(false, subtype ctx t a b)
      | (_          , FixN(o,f)  ) when t_is_val ->
         begin (* heuristic to instanciate some unification variables *)
           match a.elt with
           | FixN(ol,f) ->
              begin
                match (Norm.whnf ol).elt with
                | UVar(O,v) -> uvar_set v o
                | _ -> ()
              end
           | _ -> ()
          end;
          let ctx, o' =
            let o = Norm.whnf o in
            match o.elt with
              Succ o' -> (ctx, o')
            | _ ->
               let f o = bndr_subst f (FixN(Pos.none o, f)) in
               let f = binder_from_fun "o" f in
               let (o', ctx_names) = ownu ctx.ctx_names o t (None, f) in
               let ctx = { ctx with ctx_names } in
               (add_positive ctx o o', o')
          in
          let b = bndr_subst f (FixN(o',f)) in
          Sub_FixN_r(false, subtype ctx t a b)
      | _ ->
      match Chrono.add_time check_sub_chrono (check_sub ctx a) b with
      | Sub_Applies prf    -> prf
      | Sub_New(ctx,(a,b)) ->
      match (a.elt, b.elt) with
      (* Arrow types. *)
      | (Func(t1,a1,b1), Func(t2,a2,b2)) when t_is_val ->
         if not (Totality.sub t1 t2) then subtype_msg a.pos "Arrow clash";
         let fn x = appl None (box t) (valu None (vari None x)) in
         let name = Print.get_lambda_name t in
         let f = (None, unbox (vbind (mk_free V) name fn)) in
         let (vwit, ctx_names) = vwit ctx.ctx_names f a2 b2 in
         let ctx = { ctx with ctx_names } in
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
          let check_field l (_,p,a2) ps =
            let a1 =
              try snd (A.find l fs1) with Not_found ->
              subtype_msg p ("Product clash on label " ^ l ^ "...")
            in
            let t = unbox (t_proj None (box t) (Pos.none l)) in
            let p = subtype ctx t a1 a2 in
            p::ps
          in
          (** NOTE: subtype fields with unification variables not under
              fixpoint first to allow for inductive proof *)
          let count l a2 =
            nb_vis_uvars a2
            + (try nb_vis_uvars (snd (A.find l fs1)) with Not_found -> 0)
          in
          let fs2 = A.mapi (fun l (p,a2) -> (count l a2, p, a2)) fs2 in
          let fs2 = A.sort (fun (n,_,_) (m,_,_) -> m - n) fs2 in
          let ps = A.fold check_field fs2 [] in
          Sub_Prod(ps)
      (* Disjoint sum types. *)
      | (DSum(cs1)  , DSum(cs2)  ) when t_is_val ->
          let check_variant c (_,p,a1) ps =
            let a2 =
              try snd (A.find c cs2) with Not_found ->
              subtype_msg p ("Sum clash on constructor " ^ c ^ "...")
            in
            let name = Print.get_case_name c t in
            let f = bndr_from_fun name (fun x -> Valu(Pos.none x)) in
            let (wit, ctx_names) = vwit ctx.ctx_names f a a in
            let ctx = { ctx with ctx_names } in
            let equations =
              learn ctx.equations (Equiv(t,true,Pos.none (Valu(wit))))
            in
            let ctx = { ctx with equations } in
            let p = subtype ctx (vdot wit c) a1 a2 in
            p::ps
          in
          (** NOTE: subtype fields with unification variables not under
              fixpoint first to allow for inductive proof *)
          let count c a1 =
            nb_vis_uvars a1
            + (try nb_vis_uvars (snd (A.find c cs2)) with Not_found -> 0)
          in
          let cs1 = A.mapi (fun c (p,a1) -> (count c a1, p, a1)) cs1 in
          let cs1 = A.sort (fun (n,_,_) (m,_,_) -> m - n) cs1 in
          let ps = A.fold check_variant cs1 [] in
          Sub_DSum(ps)
      (* Universal quantification on the left. *)
      | (Univ(s,f)  , Func _     ) when not t_is_val ->
          log_sub "general subtyping";
          gen_subtype ctx a b
      | (Univ(s,f)  , _          ) ->
          let u = new_uvar ctx s in
          Sub_Univ_l(subtype ctx t (bndr_subst f u.elt) b)
      (* Existential quantification on the right. *)
      | (Func _     , Exis(s,f)  ) when not t_is_val ->
          log_sub "general subtyping";
          gen_subtype ctx a b
      | (_          , Exis(s,f)  ) ->
          let u = new_uvar ctx s in
          Sub_Exis_r(subtype ctx t a (bndr_subst f u.elt))
      (* Membership on the right. *)
      | (_          , Memb(u,b)  ) when t_is_val ->
          auto_prove ctx (Equiv(t,true,u));
          Sub_Memb_r(subtype ctx t a b)
      (* Restriction on the right. *)
      | (_          , Rest(c,e)  ) ->
         begin
           (* we learn the equation that we will prove below *)
           let prf =
             try
               let equations = learn ctx.equations e in
               Some(subtype {ctx with equations} t a c)
             with
               Contradiction -> None
           in
           auto_prove ctx e;
           Sub_Rest_r(prf)
          end
      (* Implication on the left. *)
      | (Impl(e,c)   , _        ) ->
         begin
           (* we learn the equation that we will prove below *)
           let prf =
             try
               let equations = learn ctx.equations e in
               Some(subtype {ctx with equations} t c b)
             with
               Contradiction -> None
           in
           auto_prove ctx e;
           Sub_Impl_l(prf)
          end
      (* Mu right and Nu Left, infinite case. *)
      | (_          , FixM(o,f) ) when is_conv o ->
          Sub_FixM_r(true, subtype ctx t a (bndr_subst f b.elt))
      | (FixN(o,f)  , _         ) when is_conv o ->
          Sub_FixN_l(true, subtype ctx t (bndr_subst f a.elt) b)
      (* Mu right and Nu left rules, general case. *)
      | (_          , FixM(o,f)  ) ->
          let u = new_uvar ctx O in
          let b = bndr_subst f (FixM(u,f)) in
          let prf = subtype ctx t a b in
          if not (Ordinal.less_ordi ctx.positives u o) then
            subtype_msg b.pos "ordinal not suitable (μr rule)";
          Sub_FixM_r(false, prf)
      | (FixN(o,f)  , _          ) ->
          let u = new_uvar ctx O in
          let a = bndr_subst f (FixN(u,f)) in
          let prf = subtype ctx t a b in
          if not (Ordinal.less_ordi ctx.positives u o) then
            subtype_msg b.pos "ordinal not suitable (νl rule)";
          Sub_FixN_l(false, prf)
      (* Fallback to general witness. *)
      | (_          , _          ) when not t_is_val ->
         log_sub "general subtyping";
         gen_subtype ctx a b
      (* No rule apply. *)
      | _                          ->
         subtype_msg None "No rule applies")
    in
    (t, a, b, r)
    with
    | Subtype_error _ as e -> raise e
    | e -> subtype_error t a b e
  in
  fun ctx t a b -> Chrono.add_time sub_chrono (subtype ctx t a) b

and auto_prove : ctxt -> rel -> unit =
  fun ctx rel ->
    let ctx = { ctx with in_auto = true } in
    try
      prove ctx.equations rel
    with
      Failed_to_prove(rel,bls) as exn ->
        let cmp b1 b2 = match (b1,b2) with
          | BTot _, BCas _ -> -1
          | BCas _, BTot _ -> 1
          | _     , _      -> 0
        in
        let bls = List.stable_sort cmp bls in
        let decrease_lvl ctx n =
          let (l1,l2) = ctx.auto_lvl in
          let auto_lvl =
            if n = 1 then
              if l2 <= 0 then raise exn else (l1, l2 - 1)
            else
              if l1 <= 0 then raise exn else (l1 - 1, l2)
          in
          { ctx with auto_lvl }
        in
        let rec fn bls =
          match bls with
          | [] -> raise exn
          | BTot e :: bls ->
             let ctx = decrease_lvl ctx 1 in
             let ty = unbox (rest None (prod None A.empty) (box rel)) in
             let u = valu None (reco None A.empty) in
             let f = labs None None (Pos.none "x") (fun _ -> u) in
             let t = unbox (appl None (valu None f) (Bindlib.box e)) in
             let (l1,l2) = ctx.auto_lvl in
             log_aut "totality (%d,%d): %a" l1 l2 Print.ex t;
             (try type_term ctx t ty
              with Type_error _ -> fn bls)
          | BCas(e,cs) :: bls ->
             let ctx = decrease_lvl ctx (List.length cs) in
             let ty = unbox (rest None (prod None A.empty) (box rel)) in
             let u = valu None (reco None A.empty) in
             let mk_case c = A.add c (None, Pos.none "x", (fun _ -> u)) in
             let cases = List.fold_right mk_case cs A.empty in
             let f = labs None None (Pos.none "x") (fun v ->
                            case None (vari None v) cases)
             in
             let t = unbox (appl None (valu None f) (Bindlib.box e)) in
             let (l1,l2) = ctx.auto_lvl in
             log_aut "cases    (%d,%d): %a" l1 l2 Print.ex t;
             (try type_term ctx t ty
              with Type_error _ -> fn bls)

        in ignore (fn bls)

and gen_subtype : ctxt -> prop -> prop -> sub_rule =
  fun ctx a b ->
    let f = bndr_from_fun "x" (fun x -> Valu(Pos.none x)) in
    let (eps, ctx_names) = vwit ctx.ctx_names f a b in
    let ctx = { ctx with ctx_names } in
    let wit = Pos.none (Valu eps) in
    Sub_Gene(subtype ctx wit a b)

and check_sub : ctxt -> prop -> prop -> check_sub = fun ctx a b ->
  (* Looking for potential induction hypotheses. *)
  let ihs = ctx.sub_ihs in
  log_sub "there are %i potential subtyping induction hypotheses"
    (List.length ihs);
  (* Function for finding a suitable induction hypothesis. *)
  let rec find_suitable ihs =
    match ihs with
    | ih::ihs ->
        begin
          try
            (* Elimination of the schema, and unification with goal type. *)
            let spe = elim_sub_schema ctx ih in
            let (a0, b0) = spe.sspe_judge in
            (* Check if schema applies. *)
            if not (UTimed.pure_test
                      (fun () -> unif_expr ctx a a0 && unif_expr ctx b b0)
                      ())
            then raise Exit;
            (* Check positivity of ordinals. *)
            let ok =
              List.for_all (fun (o,_) -> Ordinal.is_pos ctx.positives o)
                           spe.sspe_relat &&
              List.for_all (fun (o,o') -> Ordinal.less_ordi ctx.positives o' o)
                           spe.sspe_relat
            in
            if not ok then raise Exit;
            (* Add call to call-graph and build the proof. *)
            add_call ctx (ih.ssch_index, spe.sspe_param) true;
            Sub_Applies(Sub_Ind(ih))
          with Exit -> find_suitable ihs
        end
    | []      ->
        (* No matching induction hypothesis. *)
        let no_uvars () =
          uvars ~ignore_epsilon:true a = [] &&
          uvars ~ignore_epsilon:true b = []
        in
        log_sub "no suitable induction hypothesis";
        match a.elt, b.elt with
        (* TODO #5 to avoid the restiction uvars a = [] && uvars b = [] below,
           subml introduces unification variables parametrised by the
           generalised ordinals *)
        | ((FixM _ | FixN _), _) | (_, (FixM _ | FixN _)) when no_uvars () ->
           (* Construction of a new schema. *)
           let (sch, os) = sub_generalise ctx a b in
           (* Registration of the new top induction hypothesis and call. *)
           add_call ctx (sch.ssch_index, os) false;
           (* Recording of the new induction hypothesis. *)
           log_sub "the schema has %i arguments" (Array.length os);
           let ctx = { ctx with sub_ihs = sch :: ctx.sub_ihs } in
           (* Instantiation of the schema. *)
           let (spe, ctx) = inst_sub_schema ctx sch os in
           let ctx = {ctx with positives = spe.sspe_relat} in
           Sub_New({ctx with top_ih = (sch.ssch_index, spe.sspe_param)},
                   spe.sspe_judge)
        | _ ->
           Sub_New(ctx, (a, b))

  in find_suitable ihs

and check_fix : ctxt -> bool -> term -> (t, v) bndr -> prop -> unit -> typ_proof =
  fun ctx saf t b c ->
  (* Looking for potential induction hypotheses. *)
  let ihs = Buckets.find b ctx.fix_ihs in
  log_typ "there are %i potential fixpoint induction hypotheses"
    (List.length ihs);
  (* Function for finding a suitable induction hypothesis. *)
  let rec find_suitable ihs =
    match ihs with
    | ih::ihs ->
       begin
         try
           (* An induction hypothesis has been found. *)
           let spe = elim_fix_schema ctx ih in
           log_typ "an induction hypothesis has been found, trying";
           log_typ "   %a\n < %a" Print.ex (snd spe.fspe_judge) Print.ex c;
           let prf =
             Chrono.add_time type_chrono (subtype ctx t (snd spe.fspe_judge)) c
           in
           log_typ "it matches\n%!";
           (* Add call to call-graph and build the proof. *)
           if Totality.is_term ctx.totality && saf then
             add_call ctx (ih.fsch_index, spe.fspe_param) true;
           (t, c, Typ_Ind(ih,prf))
         with Subtype_error _ | Exit -> find_suitable ihs
       end
    | []      ->
       (* No matching induction hypothesis. *)
       log_typ "no suitable induction hypothesis";
       type_error (E(T,t)) c (No_typing_IH(bndr_name b))
  in
  if ihs = [] then
    begin
      (* Construction of a new schema. *)
      let (sch, os) = fix_generalise ctx b c in
      (* Registration of the new top induction hypothesis and call. *)
      add_call ctx (sch.fsch_index, os) false;
      (* Recording of the new induction hypothesis. *)
      log_typ "the schema has %i arguments" (Array.length os);
      let ctx =
        if os = [||] then ctx
        else { ctx with fix_ihs = Buckets.add b sch ctx.fix_ihs }
      in
      (* Instantiation of the schema. *)
      let (spe, ctx) = inst_fix_schema ctx sch os in
      let ctx = {ctx with top_ih = (sch.fsch_index, spe.fspe_param)} in
      (* Unrolling of the fixpoint and proof continued. *)
      let v = bndr_subst b t.elt in
      (fun () ->
        Chrono.add_time type_chrono (type_valu ctx v) (snd spe.fspe_judge))
    end
  else
    let res = find_suitable ihs in (fun () -> res)

(** function building the relations between ordinals *)
and get_relat  : ordi array -> (int * int) list =
  fun os ->
    let l = ref [] in
    Array.iteri (fun i o ->
      let rec gn o = match (Norm.whnf o).elt with
        | OWMu{valu={contents = (o',_,_)}}
        | OWNu{valu={contents = (o',_,_)}}
        | OSch(_,Some o',_)
        | Succ(o') ->
           (try hn (Array.length os - 1) o' with Not_found -> gn o')
        | _ -> ()
      and hn j o' =
        if eq_expr o' os.(j) then l:= (j,i)::!l
        else if j > 0 then hn (j-1) o' else raise Not_found
      in
      gn o
      ) os;
    !l

(* Generalisation (construction of a fix_schema). *)
and sub_generalise : ctxt -> prop -> prop -> sub_schema * ordi array =
  fun ctx b c ->
    (* Extracting ordinal parameters from the goal type. *)
    let (ssch_judge, os) = Misc.bind2_ordinals b c in

    (* build the relations *)
    let ssch_relat = get_relat os in
    (* only keep the relations with a positive ordinals *)
    let is_posit (i,_) = Ordinal.is_pos ctx.positives os.(i) in
    let ssch_relat = List.filter is_posit ssch_relat in

    (* Build the judgment. *)
    (* Output.bug_msg "Schema: %a" Print.omb omb;*)

    (* Ask for a fresh symbol index. *)
    let ssch_index =
      let names = mbinder_names ssch_judge in
      Scp.create_symbol ctx.callgraph "$" names
    in
    (* Assemble the schema. *)
    ({ssch_index ; ssch_relat ; ssch_judge}, os)

(* Generalisation (construction of a fix_schema). *)
and fix_generalise : ctxt -> (t, v) bndr -> prop -> fix_schema * ordi array =
  fun ctx b c ->
    (* Extracting ordinal parameters from the goal type. *)
    let (omb, os) = Misc.bind_spos_ordinals c in

    (* Build the judgment. *)
    (* Output.bug_msg "Schema: %a" Print.omb omb; *)
    let fsch_judge = (b, omb) in
    (* Ask for a fresh symbol index. *)
    let fsch_index =
      let name  = (bndr_name b).elt in
      let names = mbinder_names omb in
      Scp.create_symbol ctx.callgraph name names
    in
    (* Assemble the schema. *)
    ({fsch_index ; fsch_judge}, os)

(* Elimination of a schema using ordinal unification variables. *)
and elim_fix_schema : ctxt -> fix_schema -> fix_specialised =
  fun ctx sch ->
    let arity = mbinder_arity (snd sch.fsch_judge) in
    let fspe_param = Array.init arity (fun _ -> new_uvar ctx O) in
    let xs = Array.map (fun e -> e.elt) fspe_param in
    let a = msubst (snd sch.fsch_judge) xs in
    let fspe_judge = (fst sch.fsch_judge, a) in
    { fspe_param ; fspe_judge }

(* Elimination of a schema using ordinal unification variables. *)
and elim_sub_schema : ctxt -> sub_schema -> sub_specialised =
  fun ctx sch ->
    let arity = mbinder_arity sch.ssch_judge in
    let sspe_param = Array.init arity (fun _ -> new_uvar ctx O) in
    let xs = Array.map (fun e -> e.elt) sspe_param in
    let sspe_judge = msubst sch.ssch_judge xs in
    let sspe_relat = List.map (fun (i,j) -> (sspe_param.(i),sspe_param.(j)))
                              sch.ssch_relat
    in
    { sspe_param ; sspe_relat; sspe_judge }

(* Instantiation of a schema with ordinal witnesses. *)
and inst_fix_schema : ctxt -> fix_schema -> ordi array
                      -> fix_specialised * ctxt =
  fun ctx sch os ->
    let arity = mbinder_arity (snd sch.fsch_judge) in
    let (eps, ctx_names) = cwit ctx.ctx_names (FixSch sch) in
    let ctx = { ctx with ctx_names } in
    let rec fn i = osch i None eps in
    let fspe_param = Array.init arity fn in
    let xs = Array.map (fun e -> e.elt) fspe_param in
    let a = msubst (snd sch.fsch_judge) xs in
    let fspe_judge = (fst sch.fsch_judge, a) in
    ({ fspe_param ; fspe_judge }, ctx)

(* Instantiation of a schema with ordinal witnesses. *)
and inst_sub_schema : ctxt -> sub_schema -> ordi array
                      -> sub_specialised * ctxt =
  fun ctx sch os ->
    let arity = mbinder_arity sch.ssch_judge in
    let (eps, ctx_names) = cwit ctx.ctx_names (SubSch sch) in
    let cache = ref [] in
    let rec fn i =
      try List.assoc i !cache with Not_found ->
        let bound = try Some (fn (List.assoc i sch.ssch_relat))
                    with Not_found -> None in
        let res = osch i bound eps in
        cache := (i,res)::!cache;
        res
    in
    let sspe_param = Array.init arity fn in
    let xs = Array.map (fun e -> e.elt) sspe_param in
    let sspe_judge = msubst sch.ssch_judge xs in
    let sspe_relat = List.map (fun (i,j) -> (sspe_param.(i),sspe_param.(j)))
                              sch.ssch_relat
    in
    ({ sspe_param ; sspe_relat; sspe_judge }, ctx)

(* Add a call to the call-graph. *)
and add_call : ctxt -> (Scp.index * ordi array) -> bool -> unit =
  fun ctx callee is_rec ->
    let todo () =
      let caller = ctx.top_ih in
      let matrix = build_matrix ctx.callgraph ctx.positives callee caller in
      let callee = fst callee in
      let caller = fst caller in
      Scp.(add_call ctx.callgraph { callee ; caller ; matrix ; is_rec })
    in
    UTimed.(ctx.add_calls := todo :: !(ctx.add_calls))

(* Build a call-matrix given the caller and the callee. *)
and build_matrix : Scp.t -> (ordi * ordi) list ->
                     (Scp.index * ordi array) ->
                     (Scp.index * ordi array) ->
                     Scp.matrix = fun calls pos callee caller ->
  let open Scp in
  let w = Scp.arity (fst callee) calls in
  let h = Scp.arity (fst caller) calls in
  let tab = Array.init h (fun _ -> Array.make w Infi) in
  let square = fst callee = fst caller in

  let fn j oj i oi =
    assert(j < h); assert(i < w);
    let r =
      if Ordinal.less_ordi pos oi oj then Min1
      else if Ordinal.leq_ordi pos oi oj then Zero
      else Infi
    in
    tab.(j).(i) <- r
  in
  (** Heuristic: diagonal first, for better guess when unification
      variable remain.  Check: we can put a -1 in this case ?  *)
  if square then
    Array.iteri (fun j oj ->
        fn j oj j (snd callee).(j)) (snd caller);
  Array.iteri (fun j oj ->
      Array.iteri (fun i oi -> if not square || i != j then fn j oj i oi)
                  (snd callee)) (snd caller);
  { w ; h ; tab }

and type_valu : ctxt -> valu -> prop -> typ_proof = fun ctx v c ->
  let t = Pos.make v.pos (Valu(v)) in
  log_typ "proving the value judgment:\n  %a\n  ⊢ %a\n  : %a"
    print_pos ctx.positives Print.ex v Print.ex c;
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
       let a =
         match ao with
         | None   -> new_uvar ctx P
         | Some a -> a
       in
       let b = new_uvar ctx P in
       let tot = Totality.new_tot () in
       let c' = Pos.none (Func(tot,a,b)) in
       let p1 = subtype ctx t c' c in
       log_typ "arrow tot: %a" Print.arrow tot;
       let (wit,ctx_names) = vwit ctx.ctx_names f a b in
       let ctx = { ctx with ctx_names; totality = tot } in
       let twit = Pos.none(Valu wit) in
       (* Learn the equivalence that are valid in the witness. *)
       begin
         try
           let ctx = learn_nobox ctx wit in
           let ctx = learn_equivalences ctx wit a in
           let ctx = learn_neg_equivalences ctx v (Some twit) c in
           log_typ "arrow tot2: %a" Print.arrow tot;
           let p2 = type_term ctx (bndr_subst f wit.elt) b in
           Typ_Func_i(p1,Some p2)
         with Contradiction ->
           warn_unreachable ctx (bndr_subst f wit.elt);
           Typ_Func_i(p1, None)
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
    | Coer(_,v,a) ->
        let t = Pos.make v.pos (Valu(v)) in
        let p1 = subtype ctx t a c in
        let ctx = learn_neg_equivalences ctx v None c in
        let p2 = type_valu ctx v a in
        Typ_VTyp(p1,p2)
    (* Such that. *)
    | Such(_,_,r) ->
        let (a,v) = instantiate ctx r.binder in
        let (b,wopt) =
          match r.opt_var with
          | SV_None    -> (c                  , Some(t))
          | SV_Valu(v) -> (extract_vwit_type v, Some(Pos.none (Valu v)))
          | SV_Stac(s) -> (extract_swit_type s, None)
        in
        let _ =
          try
            match wopt with
            | None   -> ignore(gen_subtype ctx b a)
            | Some t -> ignore(subtype ctx t b a)
          with _ -> cannot_unify b a
        in Typ_TSuch(type_valu ctx v c)
    (* Set auto lvl *)
    | PSet(l,_,v) ->
        begin
          let (ctx, restore) = do_set_param ctx l in
          try
            let p = type_valu ctx v c in
            restore ();
            Typ_TSuch(p)
          with e -> restore (); raise e
        end
    (* Witness. *)
    | VWit(w)     ->
        let (_,a,_) = !(w.valu) in
        let (b, equations) = check_nobox v ctx.equations in
        assert b;
        let p = subtype {ctx with equations} t a c in
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
        wrn_msg "goal %S %a" str Pos.print_short_pos_opt v.pos;
        Typ_Goal(str)
    | UWit(_)     ->
        begin try
          let v = to_vwit (Pos.none (Valu v)) ctx.equations in
          Typ_TSuch(type_valu ctx v c)
        with Not_found ->
             unexpected "∀-witness during typing..."
        end
    | EWit(_)     ->
        begin try
          let v = to_vwit (Pos.none (Valu v)) ctx.equations in
          Typ_TSuch(type_valu ctx v c)
        with Not_found ->
             unexpected "∃-witness during typing..."
        end
    | UVar(_,v)   ->
        begin match !(v.uvar_val) with
        | Set v -> Typ_TSuch(type_valu ctx v c)
        | _     -> unexpected "unification variable during typing..."
        end
    (* Constructors that cannot appear in user-defined terms. *)
    | VPtr(_)     -> unexpected "VPtr during typing..."
    | Vari(_)     -> unexpected "Free variable during typing..."
    | Dumm(_)     -> unexpected "Dummy value during typing..."
    | ITag(_)     -> unexpected "ITag during typing..."
  in (Pos.make v.pos (Valu(v)), c, r)
  with
  | Type_error _ as e -> raise e
  | e -> type_error (E(V,v)) c e

and do_set_param ctx = function
  | Alvl(b,d) ->
     let ctx = { ctx with auto_lvl = (b,d) } in
     (ctx, fun () -> ())
  | Logs(s)   ->
     let save = Log.get_enabled () in
     Log.set_enabled s;
     (ctx, fun () -> Log.set_enabled save)

and is_typed : type a. a v_or_t -> a ex loc -> bool = fun t e ->
  let e = Norm.whnf e in
  match (t,e.elt) with
  | _, Coer(_,_,a)     -> uvars a = []
  | _, VWit(w)         -> !(w.vars) = []
  | _, Appl(t,_)       -> is_typed VoT_T t
  | _, Valu(v)         -> is_typed VoT_V v
  | _, Proj(v,_)       -> is_typed VoT_V v
  | _, Cons(_,v)       -> is_typed VoT_V v
  | _, VDef _          -> true
  | _                  -> false

and warn_unreachable ctx t =
  if not (is_scis t) && not (ctx.in_auto) then
    begin
      match t.pos with
      | None   -> Output.wrn_msg "unreachable code..."
      | Some p -> Output.wrn_msg "unreachable code %a"
                                 Pos.print_short_pos p
    end;

and type_term : ctxt -> term -> prop -> typ_proof = fun ctx t c ->
  log_typ "proving the term judgment:\n  %a\n  ⊢(%a) %a\n  : %a"
    print_pos ctx.positives Print.arrow ctx.totality Print.ex t Print.ex c;
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
    | Appl(f,u)   ->
        (* try to get the type of u. usefull in let syntactic sugar *)
        let a = match (Norm.whnf t).elt with
          | Valu{elt = LAbs(Some a, _)} -> a
          | _ -> new_uvar ctx P
        in
        let (is_val, _, ctx) = term_is_value u ctx in
        let tot = ctx.totality in
        let (ae, strong) =
          if is_val || not (Totality.is_not_tot tot) then
            (Pos.none (Memb(u, a)), true) else (a, false)
        in
        log_typ "strong: %b" strong;
        let (p1,p2) =
          if is_typed VoT_T t && not (is_typed VoT_T u) then
            let p1 = type_term ctx f (Pos.none (Func(tot,ae,c))) in
            let p2 = type_term ctx u a in
            (p1,p2)
          else
            let p2 = type_term ctx u a in
            let p1 = type_term ctx f (Pos.none (Func(tot,ae,c))) in
            (p1,p2)
        in
        if is_val then Typ_Func_s(p1,p2) else Typ_Func_e(p1,p2)
    (* Fixpoint *)
    | FixY(saf,b) ->
       let rec break_univ ctx c =
         match (Norm.whnf c).elt with
         | Univ(O,f) -> let (eps, ctx_names) = uwit ctx.ctx_names O t f in
                        let ctx = { ctx with ctx_names } in
                        break_univ ctx (bndr_subst f eps.elt)
         | _         -> (c, ctx)
       in
       let (c, ctx) = break_univ ctx c in
       let p =
         Chrono.add_time check_fix_chrono (check_fix ctx saf t b) c ()
       in
       Typ_FixY(p)
    (* μ-abstraction. *)
    | MAbs(b)     ->
        let (eps, ctx_names) = swit ctx.ctx_names b c in
        let ctx = { ctx with ctx_names } in
        let t = bndr_subst b eps.elt in
        Typ_Mu(type_term ctx t c)
    (* Named term. *)
    | Name(pi,u)  ->
        let ctx = check_total ctx t c in
        let a = new_uvar ctx P in
        (* type stack before seems better, generate subtyping
           constraints in the correct direction *)
        let p1 = type_stac ctx pi a in
        let p2 = type_term ctx u a in
        Typ_Name(p2,p1)
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
        let check d (p,f) ps =
          log_typ "Checking case %s." d;
          let (_,a) = A.find d ts in
          let vd = vdot v d in
          let a = Pos.none (Memb(vd, a)) in
          let (wit, ctx_names) = vwit ctx.ctx_names f a c in
          let ctx = { ctx with ctx_names } in
          let t = bndr_subst f wit.elt in
          (try
            let ctx = learn_nobox ctx wit in
            let equations =
              let t1 = Pos.none (Valu(Pos.none (Cons(Pos.none d, wit)))) in
              let t2 = Pos.none (Valu(v)) in
              learn ctx.equations (Equiv(t1,true,t2))
            in
            let ctx = { ctx with equations } in
            let ctx = learn_equivalences ctx wit a in
            (fun () -> type_term ctx t c :: ps)
          with Contradiction ->
            warn_unreachable ctx t;
            (fun () -> (t,c,Typ_Scis)::ps)) ()
        in
        let ps = A.fold check m [] in
        Typ_DSum_e(p,List.rev ps)
    (* Coercion. *)
    | Coer(_,t,a)   ->
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
    (* Such that. *)
    | Such(_,_,r) ->
        let (a,t) = instantiate ctx r.binder in
        let (b,wopt) =
          match r.opt_var with
          | SV_None    -> (c                  , Some(t))
          | SV_Valu(v) -> (extract_vwit_type v, Some(Pos.none (Valu v)))
          | SV_Stac(s) -> (extract_swit_type s, None)
        in
        let _ =
          try
            match wopt with
            | None   -> ignore(gen_subtype ctx b a)
            | Some t -> ignore(subtype ctx t b a)
          with _ -> cannot_unify b a
        in Typ_TSuch(type_term ctx t c)
    (* Set auto lvl *)
    | PSet(l,_,t) ->
        begin
          let (ctx, restore) = do_set_param ctx l in
          try
            let p = type_term ctx t c in
            restore ();
            Typ_TSuch(p)
          with e -> restore (); raise e
        end
    (* Definition. *)
    | HDef(_,d)   ->
        begin
          try let (_, _, r) = type_term ctx d.expr_def c in r
          with e -> type_error (E(T,t)) c e
        end
    (* Goal. *)
    | Goal(_,str) ->
        wrn_msg "goal %S %a" str Pos.print_short_pos_opt t.pos;
        Typ_Goal(str)
    (* Printing. *)
    | Prnt(_)     ->
        let a = unbox (strict_prod None A.empty) in
        let p = gen_subtype ctx a c in
        Typ_Prnt((t, a, c, p))
    (* Replacement. *)
    | Repl(t,u,p) ->
        let p1 = type_term ctx u c in
        let eq =
          let un = unbox (strict_prod None A.empty) in
          Pos.none (Rest(un,Equiv(t,true,u)))
        in
        let p2 = type_term { ctx with totality = Totality.Tot } p eq in
        Typ_Repl(p1,p2)
    | Delm(t)     ->
       let is_bot  = try ignore(gen_subtype ctx c Ast.bottom); true
                     with _ -> false
       in
       let pure = is_bot ||
                    Pure.(pure t && pure c
                        && Lazy.force ctx.equations.pool.pure)
       in
       let ctx =
         if pure then { ctx with totality = Totality.new_tot () } else ctx
       in
       Typ_Delm(type_term ctx t c)
    | UWit(_)     ->
        begin try
          let v = to_vwit t ctx.equations in
          Typ_TSuch(type_valu ctx v c)
        with Not_found ->
             unexpected "∀-witness during typing..."
        end
    | EWit(_)     ->
        begin try
          let v = to_vwit t ctx.equations in
          Typ_TSuch(type_valu ctx v c)
        with Not_found ->
             unexpected "∃-witness during typing..."
        end
    | UVar(_,v)   ->
        begin match !(v.uvar_val) with
        | Set t -> Typ_TSuch(type_term ctx t c)
        | _     -> unexpected "unification variable during typing..."
        end
    (* Constructors that cannot appear in user-defined terms. *)
    | TPtr(_)     -> unexpected "TPtr during typing..."
    | Vari(_)     -> unexpected "Free variable during typing..."
    | Dumm(_)     -> unexpected "Dummy value during typing..."
    | ITag(_)     -> unexpected "ITag during typing..."
  in (t, c, r)
  with
  | Type_error _ as e -> raise e
  | e                 -> type_error (E(T,t)) c e

and check_total : ctxt -> term -> prop -> ctxt =
  fun ctx t c ->
    let (is_val, no_box, ctx) = term_is_value t ctx in
    if (not is_val && not no_box && not (Totality.is_not_tot ctx.totality))
    then type_error (E(T,t)) c Not_total
    else ctx

and type_stac : ctxt -> stac -> prop -> stk_proof = fun ctx s c ->
  log_typ "proving the stack judgment:\n  %a\n  stk ⊢ %a\n  : %a"
    print_pos ctx.positives Print.ex s Print.ex c;
  try
  let r =
    match s.elt with
    (* Higher-order application. *)
    | HApp(_,_,_) ->
        begin
          try let (_, _, r) = type_stac ctx (Norm.whnf s) c in r
          with e -> type_error (E(S,s)) c e
        end
    | SWit(w)   ->
        let (_,a) = !(w.valu) in
        Stk_SWit(gen_subtype ctx c a)
    (* Definition. *)
    | HDef(_,d)   ->
        begin
          try let (_, _, r) = type_stac ctx d.expr_def c in r
          with e -> type_error (E(S,s)) c e
        end
    (* Goal *)
    | Goal(_,str) ->
        wrn_msg "goal %S %a" str Pos.print_short_pos_opt s.pos;
        Stk_Goal(str)
    (* Constructors that cannot appear in user-defined stacks. *)
    | Coer(_,_,_) -> .
    | Such(_,_,_) -> .
    | PSet(_,_,_) -> .
    | UWit(_)     -> unexpected "∀-witness during typing..."
    | EWit(_)     -> unexpected "∃-witness during typing..."
    | UVar(_)     -> unexpected "unification variable during typing..."
    | Vari(_)     -> unexpected "Free variable during typing..."
    | Dumm(_)     -> unexpected "Dummy value during typing..."
    | ITag(_)     -> unexpected "Tag during typing..."
  in (s, c, r)
  with
  | Type_error _ as e -> raise e
  | e -> type_error (E(S,s)) c e

let type_check : term -> prop -> prop * typ_proof = fun t a ->
  try
    let ctx = empty_ctxt () in
    let prf = type_term ctx t a in
    List.iter (fun f -> f ()) (List.rev !(ctx.add_calls));
    if not (Scp.scp ctx.callgraph) then loops t;
    let l = uvars a in
    assert(l = []); (* FIXME #16 *)
    reset_tbls ();
    (Norm.whnf a, prf)
  with e -> reset_tbls (); raise e

let type_check t = Chrono.add_time type_chrono (type_check t)

let is_subtype : prop -> prop -> bool = fun a b ->
  try
    let ctx = empty_ctxt () in
    let _ = gen_subtype ctx a b in
    let la = uvars a in
    let lb = uvars b in
    assert(la = []); (* FIXME #16 *)
    assert(lb = []); (* FIXME #16 *)
    List.iter (fun f -> f ()) (List.rev !(ctx.add_calls));
    let res = Scp.scp ctx.callgraph in
    reset_tbls ();
    res
  with _ ->
    reset_tbls ();
    false
