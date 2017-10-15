(** Expression comparing and unification. *)

open Bindlib
open Eq
open Sorts
open Pos
open Ast
open Output
open Print
open Uvars

(* Log functions registration. *)
let log_equ = Log.register 'c' (Some "cmp") "comparing informations"
let log_equ = Log.(log_equ.p)

(* Setting a unification variable. (not in uvars.ml: needs print) *)
let uvar_set : type a. a uvar -> a ex loc -> unit = fun u e ->
  log_uni "?%i ← %a" u.uvar_key Print.ex e;
  assert(!(u.uvar_val) = None);
  Timed.(u.uvar_val := Some e)

let full_eq = ref false

exception DontKnow
type oracle = { eq_val :v ex loc -> v ex loc -> bool;
                eq_trm :t ex loc -> t ex loc -> bool }

let default_oracle = {
    eq_val = (fun _ _ -> raise DontKnow);
    eq_trm = (fun _ _ -> raise DontKnow)
  }

type eq =
  { eq_expr     : 'a. ?oracle:oracle -> ?strict:bool ->
                    'a ex loc -> 'a ex loc -> bool
  ; eq_bndr     : 'a 'b. ?oracle:oracle -> ?strict:bool -> 'a sort ->
                    ('a,'b) bndr ->
                    ('a,'b) bndr -> bool
  ; eq_ombinder : 'a. ?oracle:oracle -> ?strict:bool ->
                    (o ex, 'a ex loc) mbinder ->
                    (o ex, 'a ex loc) mbinder -> bool }

(* Comparison function with unification variable instantiation. *)
let {eq_expr; eq_bndr; eq_ombinder} =
  let c = ref (-1) in
  let new_itag : type a. a sort -> a ex = fun s -> incr c; ITag(s,!c) in

  let rec eq_expr : type a. oracle -> bool -> a ex loc -> a ex loc -> bool =
    fun oracle strict e1 e2 ->
    let eq_expr e1 e2 = eq_expr oracle strict e1 e2 in
    let eq_bndr b1 b2 = eq_bndr oracle strict b1 b2 in
    let eq_ombinder omb1 omb2 = eq_ombinder oracle strict omb1 omb2 in
    let eq_ombinder2 omb1 omb2 = eq_ombinder2 oracle strict omb1 omb2 in
    let eq_fix_schema sch1 sch2 =
      sch1.fsch_index = sch2.fsch_index &&
      let (b1, omb1)  = sch1.fsch_judge in
      let (b2, omb2)  = sch2.fsch_judge in
      eq_bndr V b1 b2 && eq_ombinder omb1 omb2
    in
    let eq_sub_schema sch1 sch2 =
      sch1.ssch_index = sch2.ssch_index &&
      sch1.ssch_relat = sch2.ssch_relat &&
      let omb1 = sch1.ssch_judge in
      let omb2 = sch1.ssch_judge in
      eq_ombinder2 omb1 omb2
    in
    let eq_opt_expr o1 o2 = match (o1, o2) with
      | (None   , None   ) -> true
      | (Some e1, Some e2) -> eq_expr e1 e2
      | _                  -> false
    in
    let eq_schema sch1 sch2 =
      match (sch1, sch2) with
      | (FixSch s1, FixSch s2) -> eq_fix_schema s1 s2
      | (SubSch s1, SubSch s2) -> eq_sub_schema s1 s2
      | _ -> false
    in
    let e1 = Norm.whnf e1 in
    let e2 = Norm.whnf e2 in
    if e1.elt == e2.elt then true else (
    try
      match (Ast.sort e1, Ast.sort e2) with
      | (V, e1), (V,e2) -> oracle.eq_val e1 e2
      | (T, e1), (T,e2) -> oracle.eq_trm e1 e2
      | _ -> raise DontKnow
    with DontKnow ->
    if !full_eq then log_equ "comparing %a and %a" Print.ex e1 Print.ex e2;
    match (e1.elt, e2.elt) with
    | (Vari(_,x1)    , Vari(_,x2)    ) ->
        Bindlib.eq_vars x1 x2
    | (HFun(s1,_,b1) , HFun(_,_,b2)  ) -> eq_bndr s1 b1 b2
    | (HApp(s1,f1,a1), HApp(s2,f2,a2)) ->
        begin
          match eq_sort s1 s2 with
          | Eq  -> eq_expr f1 f2 && eq_expr a1 a2
          | NEq -> false
        end
    | (HDef(_,d)     , _             ) -> eq_expr d.expr_def e2
    | (_             , HDef(_,d)     ) -> eq_expr e1 d.expr_def
    | (Func(a1,b1)   , Func(a2,b2)   ) -> eq_expr a1 a2 && eq_expr b1 b2
    | (DSum(m1)      , DSum(m2)      ) ->
        A.equal (fun (_,a1) (_,a2) -> eq_expr a1 a2) m1 m2
    | (Prod(m1)      , Prod(m2)      ) ->
        A.equal (fun (_,a1) (_,a2) -> eq_expr a1 a2) m1 m2
    | (Univ(s1,b1)   , Univ(s2,b2)   ) ->
        begin
          match eq_sort s1 s2 with
          | Eq  -> eq_bndr s1 b1 b2
          | NEq -> false
        end
    | (Exis(s1,b1)   , Exis(s2,b2)   ) ->
        begin
          match eq_sort s1 s2 with
          | Eq  -> eq_bndr s1 b1 b2
          | NEq -> false
        end
    | (FixM(o1,b1)   , FixM(o2,b2)   ) -> eq_expr o1 o2 && eq_bndr P b1 b2
    | (FixN(o1,b1)   , FixN(o2,b2)   ) -> eq_expr o1 o2 && eq_bndr P b1 b2
    | (Memb(t1,a1)   , Memb(t2,a2)   ) -> eq_expr t1 t2 && eq_expr a1 a2
    | (Rest(a1,c1)   , Rest(a2,c2)   ) ->
        eq_expr a1 a2 &&
          begin
            match (c1, c2) with
            | (Equiv(t1,b1,u1), Equiv(t2,b2,u2)) ->
                b1 = b2 && eq_expr t1 t2 && eq_expr u1 u2
            | (Posit(o1)      , Posit(o2)      ) ->
               eq_expr o1 o2
            | (NoBox(v1)      , NoBox(v2)      ) ->
               eq_expr v1 v2
            | (_              , _              ) ->
                false
          end
    | (Impl(c1,a1)   , Impl(c2,a2)   ) ->
        eq_expr a1 a2 &&
          begin
            match (c1, c2) with
            | (Equiv(t1,b1,u1), Equiv(t2,b2,u2)) ->
                b1 = b2 && eq_expr t1 t2 && eq_expr u1 u2
            | (Posit(o1)      , Posit(o2)      ) ->
               eq_expr o1 o2
            | (NoBox(v1)      , NoBox(v2)      ) ->
               eq_expr v1 v2
            | (_              , _              ) ->
                false
          end
    (* NOTE type annotation ignored. *)
    | (LAbs(_,b1)   , LAbs(_,b2)    )  -> eq_bndr V b1 b2
    | (Cons(c1,v1)   , Cons(c2,v2)   ) -> c1.elt = c2.elt && eq_expr v1 v2
    | (Reco(m1)      , Reco(m2)      ) ->
        A.equal (fun (_,v1) (_,v2) -> eq_expr v1 v2) m1 m2
    | (Scis          , Scis          ) -> true
    | (VDef(d1)      , VDef(d2)      ) when d1 == d2
                                       -> true
    | (VDef(d1)      , _             ) ->
        eq_expr (Erase.to_valu d1.value_eval) e2
    | (_             , VDef(d2)      ) ->
        eq_expr e1 (Erase.to_valu d2.value_eval)
    | (Valu(v1)      , Valu(v2)      ) -> eq_expr v1 v2
    | (Appl(t1,u1)   , Appl(t2,u2)   ) -> eq_expr t1 t2 && eq_expr u1 u2
    (* NOTE type annotation ignored. *)
    | (MAbs(b1)      , MAbs(b2)      ) -> eq_bndr S b1 b2
    | (Name(s1,t1)   , Name(s2,t2)   ) -> eq_expr s1 s2 && eq_expr t1 t2
    | (Proj(v1,l1)   , Proj(v2,l2)   ) -> l1.elt = l2.elt && eq_expr v1 v2
    | (Case(v1,m1)   , Case(v2,m2)   ) ->
        let cmp (_,b1) (_,b2) = eq_bndr V b1 b2 in
        eq_expr v1 v2 && A.equal cmp m1 m2
    | (FixY(f1,v1)   , FixY(f2,v2)   ) -> eq_bndr V f1 f2 && eq_expr v1 v2
    | (Prnt(s1)      , Prnt(s2)      ) -> s1 = s2
    | (Epsi          , Epsi          ) -> true
    | (Push(v1,s1)   , Push(v2,s2)   ) -> eq_expr v1 v2 && eq_expr s1 s2
    | (Fram(t1,s1)   , Fram(t2,s2)   ) -> eq_expr t1 t2 && eq_expr s1 s2
    | (Conv          , Conv          ) -> true
    | (Succ(o1)      , Succ(o2)      ) -> eq_expr o1 o2
    (* NOTE type annotations ignored. *)
    | (Coer(_,e1,_)  , _             ) -> eq_expr e1 e2
    | (_             , Coer(_,e2,_)  ) -> eq_expr e1 e2
    | (Such(_,_,r)   , _             ) -> eq_expr (bseq_dummy r.binder) e2
    | (_             , Such(_,_,r)   ) -> eq_expr e1 (bseq_dummy r.binder)
    | (ITag(_,i1)    , ITag(_,i2)    ) -> i1 = i2
    (* NOTE should not be compare dummy expressions. *)
    | (Dumm          , Dumm          ) -> false
    | (VWit(_,w1)    , VWit(_,w2)    ) -> w1 == w2 ||
                                            (let (f1,a1,b1) = w1 in
                                             let (f2,a2,b2) = w2 in
                                             eq_bndr V f1 f2 && eq_expr a1 a2
                                             && eq_expr b1 b2)
    | (SWit(_,w1)    , SWit(_,w2)    ) -> w1 == w2 ||
                                            (let (f1,a1) = w1 in
                                             let (f2,a2) = w2 in
                                             eq_bndr S f1 f2 && eq_expr a1 a2)
    | (UWit(_,s1,w1) , UWit(_,_,w2)  ) -> w1 == w2 ||
                                            (let (t1,b1) = w1 in
                                             let (t2,b2) = w2 in
                                             eq_bndr s1 b1 b2 && eq_expr t1 t2)
    | (EWit(_,s1,w1) , EWit(_,_,w2)  ) -> w1 == w2 ||
                                            (let (t1,b1) = w1 in
                                             let (t2,b2) = w2 in
                                             eq_bndr s1 b1 b2 && eq_expr t1 t2)
    | (OWMu(_,w1)    , OWMu(_,w2)    ) -> w1 == w2 ||
                                            (let (o1,t1,b1) = w1 in
                                             let (o2,t2,b2) = w2 in
                                             eq_expr o1 o2 && eq_expr t1 t2
                                             && eq_bndr O b1 b2)
    | (OWNu(_,w1)    , OWNu(_,w2)    ) -> w1 == w2 ||
                                            (let (o1,t1,b1) = w1 in
                                             let (o2,t2,b2) = w2 in
                                             eq_expr o1 o2 && eq_expr t1 t2
                                             && eq_bndr O b1 b2)
    | (OSch(_,w1)    , OSch(_,w2)    ) -> w1 == w2 ||
                                            (let (o1,i1,s1) = w1 in
                                             let (o2,i2,s2) = w2 in
                                             i1 = i2 && eq_opt_expr o1 o2
                                             && eq_schema s1 s2)
    | (UVar(_,u1)    , UVar(_,u2)    ) ->
       if strict then u1.uvar_key = u2.uvar_key else
         begin
           if u1.uvar_key <> u2.uvar_key then uvar_set u1 e2; (* arbitrary *)
           true
         end
    | (UVar(_,u1)    , _             ) when not strict ->
       let rec remove_occur_check : type a. a ex loc -> a ex loc = fun b ->
         let b = Norm.whnf b in
         match b.elt with
         | Impl(c,e) when uvar_occurs_rel u1 c
             -> remove_occur_check e
         | Func({elt = Memb(t,a)}, b) when uvar_occurs u1 t
           -> remove_occur_check (Pos.none (Func(a,b)))
         | Func({elt = Rest(a,c)}, b) when uvar_occurs_rel u1 c
           -> remove_occur_check (Pos.none (Func(a,b)))
         | _ -> b (* NOTE #48: more cases are possible *)
       in
       let e2 = remove_occur_check e2 in
       if uvar_occurs u1 e2 then false else (uvar_set u1 e2; true)
    | (_             , UVar(_,u2)    ) when not strict ->
       let rec remove_occur_check : type a. a ex loc -> a ex loc = fun b ->
         let b = Norm.whnf b in
         match b.elt with
         | Rest(e,c) when uvar_occurs_rel u2 c ->
             remove_occur_check e
         | Memb(t,a) when uvar_occurs u2 t     ->
             remove_occur_check a
         | Func({elt = Impl(c,a)}, b) when uvar_occurs_rel u2 c ->
             remove_occur_check (Pos.none (Func(a,b)))
         | _ -> b (* NOTE #48: more cases are possible *)
       in
       let e1 = remove_occur_check e1 in
       if uvar_occurs u2 e1 then false else (uvar_set u2 e1; true)
    (* two next cases are automatically stronger with oracle *)
    | (VPtr v1       , VPtr v2       ) -> v1 = v2
    | (TPtr t1       , TPtr t2       ) -> t1 = t2
    | _                                -> false)

  and eq_bndr : type a b. oracle -> bool -> a sort ->
                            (a,b) bndr -> (a,b) bndr -> bool =
    fun oracle strict s1 b1 b2 ->
      if b1 == b2 then true else
        let t = new_itag s1 in
        eq_expr oracle strict (bndr_subst b1 t) (bndr_subst b2 t)

  and eq_ombinder : type a. oracle -> bool ->
                            (o ex, a ex loc) mbinder ->
                            (o ex, a ex loc) mbinder -> bool =
    fun oracle strict omb1 omb2 ->
      if omb1 == omb2 then true else
      let ar1 = mbinder_arity omb1 in
      let ar2 = mbinder_arity omb2 in
      if ar1 <> ar2 then false else
      let ta = Array.init ar1 (fun _ -> new_itag O) in
      eq_expr oracle strict (msubst omb1 ta) (msubst omb2 ta)

  and eq_ombinder2 : type a. oracle -> bool ->
                            (o ex, p ex loc * p ex loc) mbinder ->
                            (o ex, p ex loc * p ex loc) mbinder -> bool =
    fun oracle strict omb1 omb2 ->
      if omb1 == omb2 then true else
      let ar1 = mbinder_arity omb1 in
      let ar2 = mbinder_arity omb2 in
      if ar1 <> ar2 then false else
      let ta = Array.init ar1 (fun _ -> new_itag O) in
      let (k11, k12) = msubst omb1 ta in
      let (k21, k22) = msubst omb2 ta in
      eq_expr oracle strict k11 k21 && eq_expr oracle strict k12 k22
  in

  let compare_chrono = Chrono.create "compare" in

  let eq_expr : type a. ?oracle:oracle -> ?strict:bool ->
                          a ex loc -> a ex loc -> bool =
    fun ?(oracle=default_oracle) ?(strict=false) e1 e2 ->
      c := -1; (* Reset. *)
      let is_oracle = oracle != default_oracle in
      log_equ "showing %a === %a (%b)" Print.ex e1 Print.ex e2 is_oracle;
      (*bug_msg "sizes: %i and %i" (binary_size e1) (binary_size e2);*)
      let res = Chrono.add_time compare_chrono
                  (Timed.pure_test (eq_expr oracle strict e1)) e2 in
      log_equ "we have %a %s %a"
              Print.ex e1 (if res then "=" else "≠") Print.ex e2;
      res
  in

  let eq_bndr : type a b. ?oracle:oracle -> ?strict:bool ->
                     a sort -> (a,b) bndr -> (a,b) bndr -> bool =
    fun ?(oracle=default_oracle) ?(strict=false) s1 b1 b2 ->
      c := -1; (* Reset. *)
      Chrono.add_time compare_chrono
        (Timed.pure_test (eq_bndr oracle strict s1 b1)) b2
  in

  let eq_ombinder : type a. ?oracle:oracle -> ?strict:bool ->
                      (o ex, a ex loc) mbinder ->
                      (o ex, a ex loc) mbinder -> bool =
    fun ?(oracle=default_oracle) ?(strict=false) omb1 omb2 ->
      c := -1; (* Reset. *)
      Chrono.add_time compare_chrono
        (Timed.pure_test (eq_ombinder oracle strict omb1)) omb2
  in

  {eq_expr; eq_bndr; eq_ombinder}

let is_in : type a. a ex loc -> a ex loc list -> bool = fun e1 es ->
  List.exists (fun e2 -> eq_expr ~strict:true e1 e2) es

type compare =
  { compare_expr     : 'a. 'a ex loc -> 'a ex loc -> int
  ; compare_bndr     : 'a 'b. 'a sort -> ('a,'b) bndr -> ('a,'b) bndr -> int
  ; compare_ombinder : 'a. (o ex, 'a ex loc) mbinder ->
                       (o ex, 'a ex loc) mbinder -> int
  }

 (* Comparison function with unification variable instantiation. *)
let {compare_expr; compare_bndr; compare_ombinder} =
  let c = ref (-1) in
  let new_itag : type a. a sort -> a ex = fun s -> incr c; ITag(s,!c) in

  let rec compare_expr : type a. a ex loc -> a ex loc -> int =
    fun e1 e2 ->
    let compare_fix_schema sch1 sch2 =
      match compare sch1.fsch_index sch2.fsch_index with
      | 0 ->
         begin
           let (b1, omb1)  = sch1.fsch_judge in
           let (b2, omb2)  = sch2.fsch_judge in
           match compare_bndr V b1 b2 with
           | 0 -> compare_ombinder omb1 omb2
           | c -> c
         end
      | c -> c
    in
    let compare_sub_schema sch1 sch2 =
      match compare sch1.ssch_index sch2.ssch_index with
      | 0 ->
         begin
           match compare sch1.ssch_relat sch2.ssch_relat with
           | 0 ->
              let omb1 = sch1.ssch_judge in
              let omb2 = sch1.ssch_judge in
              compare_ombinder2 omb1 omb2
           | c -> c
         end
      | c -> c
    in
    let compare_opt_expr o1 o2 = match (o1, o2) with
      | (None   , None   ) ->  0
      | (Some e1, Some e2) -> compare_expr e1 e2
      | (None   , _      ) -> -1
      | (_      , None   ) ->  1
    in
    let compare_schema sch1 sch2 =
      match (sch1, sch2) with
      | (FixSch s1, FixSch s2) -> compare_fix_schema s1 s2
      | (SubSch s1, SubSch s2) -> compare_sub_schema s1 s2
      | (FixSch _ , _        ) -> -1
      | (_        , FixSch _ ) ->  1
    in
    let compare_cond c1 c2 =
      match (c1, c2) with
      | (Posit(o1)      , Posit(o2)      ) ->
         compare_expr o1 o2
      | (Posit _        , _              ) -> -1
      | (_              , Posit _        ) ->  1
      | (NoBox(v1)      , NoBox(v2)      ) ->
         compare_expr v1 v2
      | (NoBox _        , _              ) -> -1
      | (_              , NoBox _        ) ->  1
      | (Equiv(t1,b1,u1), Equiv(t2,b2,u2)) ->
         match compare b1 b2 with
         | 0 ->
            begin
              match compare_expr t1 t2 with
              | 0 -> compare_expr u1 u2
              | c -> c
            end
         | c -> c
    in
    let e1 = Norm.whnf e1 in
    let e2 = Norm.whnf e2 in
    if e1.elt == e2.elt then 0 else (
    match (e1.elt, e2.elt) with
    | (HDef(_,d)     , _             ) -> compare_expr d.expr_def e2
    | (_             , HDef(_,d)     ) -> compare_expr e1 d.expr_def
    | (VDef(d1)      , VDef(d2)      ) when d1 == d2
                                       -> 0
    | (VDef(d1)      , _             ) ->
        compare_expr (Erase.to_valu d1.value_eval) e2
    | (_             , VDef(d2)      ) ->
        compare_expr e1 (Erase.to_valu d2.value_eval)
    (* NOTE type annotations ignored. *)
    | (Coer(_,e1,_)  , _             ) -> compare_expr e1 e2
    | (_             , Coer(_,e2,_)  ) -> compare_expr e1 e2
    | (Such(_,_,r)   , _             ) -> compare_expr (bseq_dummy r.binder) e2
    | (_             , Such(_,_,r)   ) -> compare_expr e1 (bseq_dummy r.binder)
    | (Vari(_,x1)    , Vari(_,x2)    ) ->
       Bindlib.compare_vars x1 x2
    | (Vari _        , _             ) -> -1
    | (_             , Vari _        ) ->  1
    | (HFun(s1,_,b1) , HFun(_,_,b2)  ) -> compare_bndr s1 b1 b2
    | (HFun _        , _             ) -> -1
    | (_             , HFun _        ) ->  1
    | (HApp(s1,f1,a1), HApp(s2,f2,a2)) ->
        begin
          match compare_sort s1 s2 with
          | Eq  ->
             begin
               match compare_expr f1 f2 with
               | 0 -> compare_expr a1 a2
               | c -> c
             end
          | Lt -> -1 | Gt -> 1
        end
    | (HApp _        , _             ) -> -1
    | (_             , HApp _        ) ->  1
    | (Func(a1,b1)   , Func(a2,b2)   ) ->
       begin
         match compare_expr a1 a2 with
         | 0 -> compare_expr b1 b2
         | c -> c
       end
    | (Func _        , _             ) -> -1
    | (_             , Func _        ) ->  1
    | (DSum(m1)      , DSum(m2)      ) ->
       A.compare (fun (_,a1) (_,a2) -> compare_expr a1 a2) m1 m2
    | (DSum _        , _             ) -> -1
    | (_             , DSum _        ) ->  1
    | (Prod(m1)      , Prod(m2)      ) ->
       A.compare (fun (_,a1) (_,a2) -> compare_expr a1 a2) m1 m2
    | (Prod _        , _             ) -> -1
    | (_             , Prod _        ) ->  1
    | (Univ(s1,b1)   , Univ(s2,b2)   ) ->
        begin
          match compare_sort s1 s2 with
          | Eq  -> compare_bndr s1 b1 b2
          | Lt -> -1 | Gt -> 1
        end
    | (Univ _        , _             ) -> -1
    | (_             , Univ _        ) ->  1
    | (Exis(s1,b1)   , Exis(s2,b2)   ) ->
        begin
          match compare_sort s1 s2 with
          | Eq  -> compare_bndr s1 b1 b2
          | Lt -> -1 | Gt -> 1
        end
    | (Exis _        , _             ) -> -1
    | (_             , Exis _        ) ->  1
    | (FixM(o1,b1)   , FixM(o2,b2)   ) ->
       begin
         match compare_expr o1 o2 with
         | 0 -> compare_bndr P b1 b2
         | c -> c
       end
    | (FixM _        , _             ) -> -1
    | (_             , FixM _        ) ->  1
    | (FixN(o1,b1)   , FixN(o2,b2)   ) ->
       begin
         match compare_expr o1 o2 with
         | 0 -> compare_bndr P b1 b2
         | c -> c
       end
    | (FixN _        , _             ) -> -1
    | (_             , FixN _        ) ->  1
    | (Memb(t1,a1)   , Memb(t2,a2)   ) ->
       begin
         match compare_expr t1 t2 with
         | 0 -> compare_expr a1 a2
         | c -> c
       end
    | (Memb _        , _             ) -> -1
    | (_             , Memb _        ) ->  1
    | (Rest(a1,c1)   , Rest(a2,c2)   ) ->
       begin
         match compare_expr a1 a2 with
         | 0 -> compare_cond c1 c2
         | c -> c
       end
    | (Rest _        , _             ) -> -1
    | (_             , Rest _        ) ->  1
    | (Impl(c1,a1)   , Impl(c2,a2)   ) ->
       begin
         match compare_expr a1 a2 with
         | 0 -> compare_cond c1 c2
         | c -> c
       end
    | (Impl _        , _             ) -> -1
    | (_             , Impl _        ) ->  1
     (* NOTE type annotation ignored. *)
    | (LAbs(_,b1)    , LAbs(_,b2)    ) -> compare_bndr V b1 b2
    | (LAbs _        , _             ) -> -1
    | (_             , LAbs _        ) ->  1
    | (Cons(c1,v1)   , Cons(c2,v2)   ) ->
       begin
         match compare c1.elt c2.elt with
         | 0 -> compare_expr v1 v2
         | c -> c
       end
    | (Cons _        , _             ) -> -1
    | (_             , Cons _        ) ->  1
    | (Reco(m1)      , Reco(m2)      ) ->
       A.compare (fun (_,v1) (_,v2) -> compare_expr v1 v2) m1 m2
    | (Reco _        , _             ) -> -1
    | (_             , Reco _        ) ->  1
    | (Scis          , Scis          ) ->  0
    | (Scis          , _             ) -> -1
    | (_             , Scis          ) ->  1
    | (Valu(v1)      , Valu(v2)      ) -> compare_expr v1 v2
    | (Valu _        , _             ) -> -1
    | (_             , Valu _        ) ->  1
    | (Appl(t1,u1)   , Appl(t2,u2)   ) ->
       begin
         match compare_expr t1 t2 with
         | 0 -> compare_expr u1 u2
         | c -> c
       end
    | (Appl _        , _             ) -> -1
    | (_             , Appl _        ) ->  1
    (* NOTE type annotation ignored. *)
    | (MAbs(b1)      , MAbs(b2)      ) -> compare_bndr S b1 b2
    | (MAbs _        , _             ) -> -1
    | (_             , MAbs _        ) ->  1
    | (Name(s1,t1)   , Name(s2,t2)   ) ->
       begin
         match compare_expr s1 s2 with
         | 0 -> compare_expr t1 t2
         | c -> c
       end
    | (Name _        , _             ) -> -1
    | (_             , Name _        ) ->  1
    | (Proj(v1,l1)   , Proj(v2,l2)   ) ->
       begin
         match compare l1.elt l2.elt with
         | 0 -> compare_expr v1 v2
         | c -> c
       end
    | (Proj _        , _             ) -> -1
    | (_             , Proj _        ) ->  1
    | (Case(v1,m1)   , Case(v2,m2)   ) ->
        let cmp (_,b1) (_,b2) = compare_bndr V b1 b2 in
        begin
          match compare_expr v1 v2 with
          | 0 -> A.compare cmp m1 m2
          | c -> c
        end
    | (Case _        , _             ) -> -1
    | (_             , Case _        ) ->  1
    | (FixY(f1,v1)   , FixY(f2,v2)   ) ->
       begin
         match compare_bndr V f1 f2 with
         | 0 -> compare_expr v1 v2
         | c -> c
       end
    | (FixY _        , _             ) -> -1
    | (_             , FixY _        ) ->  1
    | (Prnt(s1)      , Prnt(s2)      ) -> compare s1 s2
    | (Prnt _        , _             ) -> -1
    | (_             , Prnt _        ) ->  1
    | (Epsi          , Epsi          ) ->  0
    | (Epsi          , _             ) -> -1
    | (_             , Epsi          ) ->  1
    | (Push(v1,s1)   , Push(v2,s2)   ) ->
       begin
         match compare_expr v1 v2 with
         | 0 -> compare_expr s1 s2
         | c -> c
       end
    | (Push _        , _             ) -> -1
    | (_             , Push _        ) ->  1
    | (Fram(t1,s1)   , Fram(t2,s2)   ) ->
       begin
         match compare_expr t1 t2 with
         | 0 -> compare_expr s1 s2
         | c -> c
       end
    | (Fram _        , _             ) -> -1
    | (_             , Fram _        ) ->  1
    | (Conv          , Conv          ) ->  0
    | (Conv          , _             ) -> -1
    | (_             , Conv          ) ->  1
    | (Succ(o1)      , Succ(o2)      ) -> compare_expr o1 o2
    | (Succ _        , _             ) -> -1
    | (_             , Succ _        ) ->  1
    | (ITag(_,i1)    , ITag(_,i2)    ) -> compare i1 i2
    | (ITag _        , _             ) -> -1
    | (_             , ITag _        ) ->  1
    | (Dumm          , _             ) -> assert false
    | (_             , Dumm          ) -> assert false
    | (Goal _        , Goal _        ) ->  0 (* FIXME: warning ? *)
    | (Goal _        , _             ) -> -1
    | (_             , Goal _        ) ->  1
    | (VWit(_,w1)    , VWit(_,w2)    ) -> if w1 == w2 then 0 else
       begin
         let (f1,a1,b1) = w1 in
         let (f2,a2,b2) = w2 in
         match compare_bndr V f1 f2 with
         | 0 ->
            begin
              match compare_expr a1 a2 with
              | 0 -> compare_expr b1 b2
              | c -> c
            end
         | c -> c
       end
    | (VWit _        , _             ) -> -1
    | (_             , VWit _        ) ->  1
    | (SWit(_,w1)    , SWit(_,w2)    ) -> if w1 == w2 then 0 else
       begin
         let (f1,a1) = w1 in
         let (f2,a2) = w2 in
         match compare_bndr S f1 f2 with
         | 0 -> compare_expr a1 a2
         | c -> c
       end
    | (SWit _        , _             ) -> -1
    | (_             , SWit _        ) ->  1
    | (UWit(_,s1,w1) , UWit(_,_,w2)  ) -> if w1 == w2 then 0 else
       begin
         let (t1,b1) = w1 in
         let (t2,b2) = w2 in
         match compare_bndr s1 b1 b2 with
         | 0 -> compare_expr t1 t2
         | c -> c
       end
    | (UWit _        , _             ) -> -1
    | (_             , UWit _        ) ->  1
    | (EWit(_,s1,w1) , EWit(_,_,w2)  ) -> if w1 == w2 then 0 else
       begin
         let (t1,b1) = w1 in
         let (t2,b2) = w2 in
         match compare_bndr s1 b1 b2 with
         | 0 -> compare_expr t1 t2
         | c -> c
       end
    | (EWit _        , _             ) -> -1
    | (_             , EWit _        ) ->  1
    | (OWMu(_,w1)    , OWMu(_,w2)    ) -> if w1 == w2 then 0 else
       begin
         let (o1,t1,b1) = w1 in
         let (o2,t2,b2) = w2 in
         match compare_expr o1 o2 with
         | 0 ->
            begin
              match compare_expr t1 t2 with
              | 0 -> compare_bndr O b1 b2
              | c -> c
            end
         | c -> c
       end
    | (OWMu _        , _             ) -> -1
    | (_             , OWMu _        ) ->  1
    | (OWNu(_,w1)    , OWNu(_,w2)    ) -> if w1 == w2 then 0 else
       begin
         let (o1,t1,b1) = w1 in
         let (o2,t2,b2) = w2 in
         match compare_expr o1 o2 with
         | 0 ->
            begin
              match compare_expr t1 t2 with
              | 0 -> compare_bndr O b1 b2
              | c -> c
            end
         | c -> c
       end
    | (OWNu _        , _             ) -> -1
    | (_             , OWNu _        ) ->  1
    | (OSch(_,w1)    , OSch(_,w2)    ) -> if w1 == w2 then 0 else
       begin
         let (o1,i1,s1) = w1 in
         let (o2,i2,s2) = w2 in
         match compare i1 i2 with
         | 0 ->
            begin
              match compare_opt_expr o1 o2 with
              | 0 -> compare_schema s1 s2
              | c -> c
            end
         | c -> c
       end
    | (OSch _        , _             ) -> -1
    | (_             , OSch _        ) ->  1
    | (VPtr v1       , VPtr v2       ) -> compare v1 v2
    | (VPtr _        , _             ) -> -1
    | (_             , VPtr _        ) ->  1
    | (TPtr t1       , TPtr t2       ) -> compare t1 t2
    | (TPtr _        , _             ) -> -1
    | (_             , TPtr _        ) ->  1
    | (UVar(_,u1)    , UVar(_,u2)    ) ->
       compare u1.uvar_key u2.uvar_key)

  and compare_bndr : type a b. a sort ->
                            (a,b) bndr -> (a,b) bndr -> int =
    fun s1 b1 b2 ->
      if b1 == b2 then 0 else
        let t = new_itag s1 in
        compare_expr (bndr_subst b1 t) (bndr_subst b2 t)

  and compare_ombinder : type a. (o ex, a ex loc) mbinder ->
                                 (o ex, a ex loc) mbinder -> int =
    fun omb1 omb2 ->
      if omb1 == omb2 then 0 else
      let ar1 = mbinder_arity omb1 in
      let ar2 = mbinder_arity omb2 in
      match compare ar1 ar2 with
      | 0 ->
         let ta = Array.init ar1 (fun _ -> new_itag O) in
         compare_expr (msubst omb1 ta) (msubst omb2 ta)
      | c -> c

  and compare_ombinder2 : type a.
                            (o ex, p ex loc * p ex loc) mbinder ->
                            (o ex, p ex loc * p ex loc) mbinder -> int =
    fun omb1 omb2 ->
      if omb1 == omb2 then 0 else
      let ar1 = mbinder_arity omb1 in
      let ar2 = mbinder_arity omb2 in
      match compare ar1 ar2 with
      | 0 ->
         let ta = Array.init ar1 (fun _ -> new_itag O) in
         let (k11, k12) = msubst omb1 ta in
         let (k21, k22) = msubst omb2 ta in
         begin
           match compare_expr k11 k21 with
           | 0 -> compare_expr k12 k22
           | c -> c
         end
      | c -> c
  in

  let compare_chrono = Chrono.create "compare" in

  let compare_expr : type a. a ex loc -> a ex loc -> int =
    fun e1 e2 ->
      c := -1; (* Reset. *)
      log_equ "showing %a =w= %a" Print.ex e1 Print.ex e2;
      (*bug_msg "sizes: %i and %i" (binary_size e1) (binary_size e2);*)
      let res = Chrono.add_time compare_chrono (compare_expr e1) e2 in
      log_equ "we have %a %s %a"
              Print.ex e1
              (if res = 0 then "=" else if res < 0 then "<" else ">")
              Print.ex e2;
      res
  in

  let compare_bndr : type a b. a sort -> (a,b) bndr -> (a,b) bndr -> int =
    fun s1 b1 b2 ->
      c := -1; (* Reset. *)
      Chrono.add_time compare_chrono (compare_bndr s1 b1) b2
  in

  let compare_ombinder : type a. (o ex, a ex loc) mbinder ->
                                 (o ex, a ex loc) mbinder -> int =
    fun omb1 omb2 ->
      c := -1; (* Reset. *)
      Chrono.add_time compare_chrono (compare_ombinder omb1) omb2
  in

  {compare_expr; compare_bndr; compare_ombinder}
