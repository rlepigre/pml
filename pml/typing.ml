open Bindlib
open Sorts
open Pos
open Ast
open Equiv

exception Type_error of pos option * string
let type_error : pos option -> string -> 'a =
  fun pos msg -> raise (Type_error(pos, msg))

exception Subtype_error of pos option * string
let subtype_error : pos option -> string -> 'a =
  fun pos msg -> raise (Subtype_error(pos, msg))

exception Unexpected_error of string
let unexpected : string -> 'a =
  fun msg -> raise (Unexpected_error(msg))

type ctxt  =
  { uvar_counter : int
  ; equations    : eq_ctxt }

let empty_ctxt =
  { uvar_counter = 0
  ; equations    = () }

let new_uvar : type a. ctxt -> a sort -> ctxt * a ex loc = fun ctx s ->
  let i = ctx.uvar_counter in
  let ctx = {ctx with uvar_counter = i+1} in
  (ctx, Pos.none (UVar(i, s, ref None)))

let eq_opt : type a. (a -> a -> bool) -> a option -> a option -> bool =
  fun cmp ao bo ->
    match (ao, bo) with
    | (None  , None  ) -> true
    | (Some a, Some b) -> cmp a b
    | (_     , _     ) -> false

let eq_expr : type a. a ex loc -> a ex loc -> bool = fun e1 e2 ->
  let c = ref (-1) in
  let new_itag : type a. unit -> a ex = fun () -> incr c; ITag(!c) in
  let rec eq_expr : type a. a ex loc -> a ex loc -> bool = fun e1 e2 ->
    match ((Norm.whnf e1).elt, (Norm.whnf e2).elt) with
    | (Vari(x1)      , Vari(x2)      ) ->
        Bindlib.eq_variables x1 x2
    | (HFun(b1)      , HFun(b2)      ) ->
        let t = new_itag () in
        eq_expr (lsubst b1 t) (lsubst b2 t)
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
                   eq_expr (lsubst b1 t) (lsubst b2 t)
          | NEq -> false
        end
    | (Exis(s1,b1)   , Exis(s2,b2)   ) ->
        begin
          match eq_sort s1 s2 with
          | Eq  -> let t = new_itag () in
                   eq_expr (lsubst b1 t) (lsubst b2 t)
          | NEq -> false
        end
    | (FixM(o1,b1)   , FixM(o2,b2)   ) ->
        let t = new_itag () in
        eq_expr o1 o2 && eq_expr (lsubst b1 t) (lsubst b2 t)
    | (FixN(o1,b1)   , FixN(o2,b2)   ) ->
        let t = new_itag () in
        eq_expr o1 o2 && eq_expr (lsubst b1 t) (lsubst b2 t)
    | (Memb(t1,a1)   , Memb(t2,a2)   ) -> eq_expr t1 t2 && eq_expr a1 a2
    | (Rest(a1,eq1)  , Rest(a2,eq2)  ) ->
        let (t1,b1,u1) = eq1 and (t2,b2,u2) = eq2 in
        b1 = b2 && eq_expr a1 a2 && eq_expr t1 t2 && eq_expr u1 u2
    | (LAbs(ao1,b1)  , LAbs(ao2,b2)  ) ->
        let t = new_itag () in
        eq_opt eq_expr ao1 ao2 && eq_expr (lsubst b1 t) (lsubst b2 t)
    | (Cons(c1,v1)   , Cons(c2,v2)   ) -> c1.elt = c2.elt && eq_expr v1 v2
    | (Reco(m1)      , Reco(m2)      ) ->
        M.equal (fun (_,v1) (_,v2) -> eq_expr v1 v2) m1 m2
    | (Scis          , Scis          ) -> true
    | (Valu(v1)      , Valu(v2)      ) -> eq_expr v1 v2
    | (Appl(t1,u1)   , Appl(t2,u2)   ) -> eq_expr t1 t2 && eq_expr u1 u2
    | (MAbs(ao1,b1)  , MAbs(ao2,b2)  ) ->
        let t = new_itag () in
        eq_opt eq_expr ao1 ao2 && eq_expr (lsubst b1 t) (lsubst b2 t)
    | (Name(s1,t1)   , Name(s2,t2)   ) -> eq_expr s1 s2 && eq_expr t1 t2
    | (Proj(v1,l1)   , Proj(v2,l2)   ) -> l1.elt = l2.elt && eq_expr v1 v2
    | (Case(v1,m1)   , Case(v2,m2)   ) ->
        let cmp (_,b1) (_,b2) =
          let t = new_itag () in eq_expr (lsubst b1 t) (lsubst b2 t)
        in
        eq_expr v1 v2 && M.equal cmp m1 m2
    | (FixY(t1,v1)   , FixY(t2,v2)   ) -> eq_expr t1 t2 && eq_expr v1 v2
    | (Epsi          , Epsi          ) -> true
    | (Push(v1,s1)   , Push(v2,s2)   ) -> eq_expr v1 v2 && eq_expr s1 s2
    | (Fram(t1,s1)   , Fram(t2,s2)   ) -> eq_expr t1 t2 && eq_expr s1 s2
    | (Conv          , Conv          ) -> true
    | (Succ(o1)      , Succ(o2)      ) -> eq_expr o1 o2
    | (DPrj(t1,x1)   , DPrj(t2,x2)   ) -> x1.elt = x2.elt && eq_expr t1 t2
    | (VTyp(v1,a1)   , VTyp(v2,a2)   ) -> eq_expr v1 v2 && eq_expr a1 a2
    | (TTyp(t1,a1)   , TTyp(t2,a2)   ) -> eq_expr t1 t2 && eq_expr a1 a2
    | (VLam(s1,b1)   , VLam(s2,b2)   ) ->
        begin
          match eq_sort s1 s2 with
          | Eq  -> let t = new_itag () in
                   eq_expr (lsubst b1 t) (lsubst b2 t)
          | NEq -> false
        end
    | (TLam(s1,b1)   , TLam(s2,b2)   ) ->
        begin
          match eq_sort s1 s2 with
          | Eq  -> let t = new_itag () in
                   eq_expr (lsubst b1 t) (lsubst b2 t)
          | NEq -> false
        end
    | (ITag(i1)      , ITag(i2)      ) -> i1 = i2
    | (Dumm          , Dumm          ) -> false (* Should not be compared *)
    | (VWit(f1,a1,b1), VWit(f2,a2,b2)) ->
        let t = new_itag () in
        eq_expr (lsubst f1 t) (lsubst f2 t) && eq_expr a1 a2 && eq_expr b1 b2
    | (SWit(f1,a1)   , SWit(f2,a2)   ) ->
        let t = new_itag () in
        eq_expr (lsubst f1 t) (lsubst f2 t) && eq_expr a1 a2
    | (UWit(s1,t1,b1), UWit(s2,t2,b2)) ->
        begin
          match eq_sort s1 s2 with
          | Eq  -> let t = new_itag () in
                   eq_expr (lsubst b1 t) (lsubst b2 t) && eq_expr t1 t2
          | NEq -> false
        end
    | (EWit(s1,t1,b1), EWit(s2,t2,b2)) ->
        begin
          match eq_sort s1 s2 with
          | Eq  -> let t = new_itag () in
                   eq_expr (lsubst b1 t) (lsubst b2 t) && eq_expr t1 t2
          | NEq -> false
        end
    | (UVar(i1,_,_)  , UVar(i2,_,_)  ) -> i1 = i2
    | (UVar(_ ,_,r)  , _             ) -> r := Some e2; true
    | (_             , UVar(_ ,_,r)  ) -> r := Some e1; true
    | _                                -> false
  in eq_expr e1 e2

type typ_rule =
  | Typ_VTyp   of sub_proof * typ_proof
  | Typ_TTyp   of sub_proof * typ_proof
  | Typ_VLam   of typ_proof
  | Typ_TLam   of typ_proof
  | Typ_VWit   of sub_proof
  | Typ_DSum_i of sub_proof * typ_proof
  | Typ_Func_i of sub_proof * typ_proof
  | Typ_Func_e of typ_proof * typ_proof
  | Typ_Prod_i of sub_proof * typ_proof list
  | Typ_Prod_e of typ_proof

and  sub_rule =
  | Sub_Equal
  | Sub_Func   of sub_proof * sub_proof

and typ_proof = term * prop * typ_rule
and sub_proof = term * prop * prop * sub_rule



let rec get_lam : type a. string -> a sort -> term -> prop -> a ex =
  fun x s t c ->
    match (Norm.whnf c).elt with
    | Univ(k,f) when lbinder_name f = x ->
        get_lam x s t (lsubst f (UWit(k,t,f)))
    | Univ(k,f) ->
        begin
          match eq_sort s k with
          | Eq  -> UWit(k,t,f)
          | NEq -> assert false
        end
    | _         -> assert false



let rec subtype : ctxt -> term -> prop -> prop -> ctxt * sub_proof =
  fun ctx t a b ->
    Printf.printf "Showing: %a ∈ %a ⊆ %a\n%!"
      Print.print_ex t Print.print_ex a Print.print_ex b;
    let a = Norm.whnf a in
    let b = Norm.whnf b in
    let (ctx, r) =
      match (a.elt, b.elt) with
      (* Same types.  *)
      | _ when eq_expr a b         ->
          Printf.printf "Ici. %a = %a\n%!" Print.print_ex a Print.print_ex b;
          (ctx, Sub_Equal)
      (* Arrow types. *)
      | (Func(a1,b1), Func(a2,b2)) ->
          let fn x = appl None (box t) (valu None (vari None x)) in
          let f = (None, unbox (vbind mk_free "x" fn)) in
          let wit = Pos.none (Valu(Pos.none (VWit(f,a2,b2)))) in
          Printf.printf "Coucou 1\n%!";
          let (ctx, p1) = subtype ctx wit a2 a1 in
          Printf.printf "Coucou 2\n%!";
          let (ctx, p2) = subtype ctx (Pos.none (Appl(t, wit))) b1 b2 in
          Printf.printf "Coucou 3\n%!";
          (ctx, Sub_Func(p1,p2))
      | _                          ->
          let open Print in
          Printf.printf "ERROR: %a ⊆ %a\n%!" print_ex a print_ex b;
          assert false
    in
    (ctx, (t, a, b, r))

and type_valu : ctxt -> valu -> prop -> ctxt * typ_proof = fun ctx v c ->
  let v = Norm.whnf v in
  let t = build_pos v.pos (Valu(v)) in
  Printf.printf "Showing: val %a : %a\n%!" Print.print_ex v Print.print_ex c;
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
        let (ctx, p2) = type_term ctx (lsubst f wit) b in
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
        let a = get_lam (lbinder_name b) s t c in
        let (ctx, p) = type_valu ctx (lsubst b a) c in
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
  Printf.printf "Showing: trm %a : %a\n%!" Print.print_ex t Print.print_ex c;
  let (ctx, r) =
    match (Norm.whnf t).elt with
    (* Value. *)
    | Valu(v)     ->
        let (ctx, (_, _, r)) = type_valu ctx v c in (ctx, r)
    (* Application. *)
    | Appl(t,u)   ->
        let (ctx, a) = new_uvar ctx P in
        let (ctx, p1) = type_term ctx t (Pos.none (Func(a,c))) in
        let (ctx, p2) = type_term ctx u a in
        (ctx, Typ_Func_e(p1,p2))
    (* μ-abstraction. *)
    | MAbs(ao,b)  ->
        assert false (* TODO *)
    (* Named term. *)
    | Name(pi,t)  ->
        assert false (* TODO *)
    (* Projection. *)
    | Proj(v,l)   ->
        let c = Pos.none (Prod(M.singleton l.elt (None, c))) in
        let (ctx, p) = type_valu ctx v c in
        (ctx, Typ_Prod_e(p))
    (* Case analysis. *)
    | Case(v,m)   ->
        assert false (* TODO *)
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
        let a = get_lam (lbinder_name b) s t c in
        let (ctx, p) = type_term ctx (lsubst b a) c in
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

let type_check : term -> prop option -> typ_proof = fun t ao -> 
  let ctx = empty_ctxt in
  let (ctx, a) = 
    match ao with
    | None   -> new_uvar ctx P
    | Some a -> (ctx, a)
  in
  snd (type_term ctx t a)
