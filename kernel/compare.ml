(** Expression comparing and unification. *)

open Bindlib
open Sorts
open Pos
open Ast
open Output
open Print

(* Log functions registration. *)
let log_equ = Log.register 'c' (Some "cmp") "comparing informations"
let log_equ = Log.(log_equ.p)

let log_uni = Log.register 'u' (Some "uni") "unification informations"
let log_uni = Log.(log_uni.p)

(* Code instrumentation (rough size of expression). *)
let binary_size : type a. a -> int = fun e ->
  let open Marshal in
  String.length (to_string e [Closures])

(* Setting a unification variable. *)
let uvar_set : type a. a uvar -> a ex loc -> unit = fun u e ->
  log_uni "?%i ← %a" u.uvar_key Print.ex e;
  assert(!(u.uvar_val) = None);
  Timed.(u.uvar_val := Some e)

(* Unification variable equality test. *)
let uvar_eq : type a. a uvar -> a uvar -> bool =
  fun u v -> u.uvar_key == v.uvar_key

type uvar_fun = { f : 'a. 'a sort -> 'a uvar -> unit }

type b = A : 'a ex -> b

let uvar_iter : type a. bool -> uvar_fun -> a ex loc -> unit =
  fun ignore_epsilon f e ->
  let not_closed b = not (Bindlib.binder_closed (snd b)) in
  let adone = Ahash.create 67 in
  let todo : type a . a ex loc -> bool =
  fun e ->
      not (ignore_epsilon) &&
        if Ahash.mem adone (A e.elt) then false
        else (
          Ahash.add adone (A e.elt) ();
          true)
  in
  let rec uvar_iter : type a. a ex loc -> unit = fun e ->
    let uvar_iter_cond c =
      match c with
      | Equiv(t,_,u) -> uvar_iter t; uvar_iter u
      | NoBox(v)     -> uvar_iter v;
      | Posit(o)     -> uvar_iter o
    in
    let buvar_iter b = if not_closed b then uvar_iter (bndr_subst b Dumm) in
    let e = Norm.whnf e in
    match e.elt with
    | Vari(_)     -> ()
    | HFun(_,_,b) -> buvar_iter b
    | HApp(_,a,b) -> uvar_iter a; uvar_iter b
    | HDef(_)     -> () (* NOTE no unification variable in definition. *)
    | Func(a,b)   -> uvar_iter a; uvar_iter b
    | Prod(m)     -> A.iter (fun _ (_,a) -> uvar_iter a) m
    | DSum(m)     -> A.iter (fun _ (_,a) -> uvar_iter a) m
    | Univ(_,b)   -> buvar_iter b
    | Exis(_,b)   -> buvar_iter b
    | FixM(o,b)   -> uvar_iter o; buvar_iter b
    | FixN(o,b)   -> uvar_iter o; buvar_iter b
    | Memb(t,a)   -> uvar_iter t; uvar_iter a
    | Rest(a,c)   -> uvar_iter a; uvar_iter_cond c
    | Impl(c,a)   -> uvar_iter_cond c; uvar_iter a
    (* NOTE type annotation ignored. *)
    | LAbs(_,b)   -> buvar_iter b
    | Cons(_,v)   -> uvar_iter v
    | Reco(m)     -> A.iter (fun _ (_,a) -> uvar_iter a) m
    | Scis        -> ()
    | VDef(_)     -> () (* NOTE no unification variable in definition. *)
    | Valu(v)     -> uvar_iter v
    | Appl(t,u)   -> uvar_iter t; uvar_iter u
    (* NOTE type annotation ignored. *)
    | MAbs(b)     -> buvar_iter b
    | Name(s,t)   -> uvar_iter s; uvar_iter t
    | Proj(v,_)   -> uvar_iter v
    | Case(v,m)   -> let fn _ (_,b) = buvar_iter b in
                     uvar_iter v; A.iter fn m
    | FixY(f,v)   -> buvar_iter f; uvar_iter v
    | Prnt(_)     -> ()
    | Epsi        -> ()
    | Push(v,s)   -> uvar_iter v; uvar_iter s
    | Fram(t,s)   -> uvar_iter t; uvar_iter s
    | Zero        -> ()
    | Conv        -> ()
    | Succ(o)     -> uvar_iter o
    (* NOTE type annotations ignored. *)
    | VTyp(v,_)   -> uvar_iter v
    | TTyp(t,_)   -> uvar_iter t
    | VLam(_,b)   -> buvar_iter b
    | TLam(_,b)   -> buvar_iter b
    | ITag(_)     -> ()
    | Dumm        -> ()
    | Goal(_)     -> ()
    | VWit(f,a,b) -> if todo e then (buvar_iter f; uvar_iter a; uvar_iter b)
    | SWit(b,a)   -> if todo e then (buvar_iter b; uvar_iter a)
    | UWit(_,t,b) -> if todo e then (uvar_iter t; buvar_iter b)
    | EWit(_,t,b) -> if todo e then (uvar_iter t; buvar_iter b)
    | OWMu(o,t,b) -> if todo e then (uvar_iter o; uvar_iter t; buvar_iter b)
    | OWNu(o,t,b) -> if todo e then (uvar_iter o; uvar_iter t; buvar_iter b)
    | OSch(o,i,s) -> if todo e then
                       begin
                         match s with
                         | FixSch s ->
                            let (t,b) = s.fsch_judge in
                            let (_,t) = Bindlib.unbind (mk_free V) (snd t) in
                            let (_,k) = Bindlib.unmbind (mk_free O) b in
                            Extra.Option.iter uvar_iter o; uvar_iter t; uvar_iter k
                         | SubSch s ->
                            let b = s.ssch_judge in
                            let (_,(k1,k2)) = Bindlib.unmbind (mk_free O) b in
                            Extra.Option.iter uvar_iter o; uvar_iter k1; uvar_iter k2
                       end
    | UVar(s,u)   -> f.f s u
  in uvar_iter e

type s_elt = U : 'a sort * 'a uvar -> s_elt

let uvars : type a. ?ignore_epsilon:bool -> a ex loc -> s_elt list =
  fun ?(ignore_epsilon=false) e ->
  let uvars = ref [] in
  let f s u =
    let p (U(_,v)) = v.uvar_key == u.uvar_key in
    if not (List.exists p !uvars) then uvars := (U(s,u)) :: !uvars
  in
  uvar_iter ignore_epsilon {f} e; !uvars

let occur_chrono = Chrono.create "occur"

let uvar_occurs : type a b. a uvar -> b ex loc -> bool = fun u e ->
  let f _ v =
    if v.uvar_key == u.uvar_key then
      begin
        log_equ "Occur check on %d" u.uvar_key;
        raise Exit
      end
  in
  try Chrono.add_time occur_chrono (uvar_iter false {f}) e; false with Exit -> true

let uvar_occurs_cond : type a. a uvar -> cond -> bool = fun u c ->
  match c with
  | Equiv(t,_,s) -> uvar_occurs u t || uvar_occurs u s
  | NoBox(v)     -> uvar_occurs u v;
  | Posit(o)     -> uvar_occurs u o

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
      sch1.fsch_posit = sch2.fsch_posit &&
      sch1.fsch_relat = sch2.fsch_relat &&
      let (b1, omb1)  = sch1.fsch_judge in
      let (b2, omb2)  = sch2.fsch_judge in
      eq_bndr V b1 b2 && eq_ombinder omb1 omb2
    in
    let eq_sub_schema sch1 sch2 =
      sch1.ssch_index = sch2.ssch_index &&
      sch1.ssch_posit = sch2.ssch_posit &&
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
    | (Zero          , Zero          ) -> true
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
    | (ITag(_,i1)    , ITag(_,i2)    ) -> i1 = i2
    (* NOTE should not be compare dummy expressions. *)
    | (Dumm          , Dumm          ) -> false
    | (VWit(f1,a1,b1), VWit(f2,a2,b2)) ->
        eq_bndr V f1 f2 && eq_expr a1 a2 && eq_expr b1 b2
    | (SWit(f1,a1)   , SWit(f2,a2)   ) -> eq_bndr S f1 f2 && eq_expr a1 a2
    | (UWit(s1,t1,b1), UWit(_,t2,b2) ) -> eq_bndr s1 b1 b2 && eq_expr t1 t2
    | (EWit(s1,t1,b1), EWit(_,t2,b2) ) -> eq_bndr s1 b1 b2 && eq_expr t1 t2
    | (OWMu(o1,t1,b1), OWMu(o2,t2,b2)) -> eq_expr o1 o2 && eq_expr t1 t2
                                          && eq_bndr O b1 b2
    | (OWNu(o1,t1,b1), OWNu(o2,t2,b2)) -> eq_expr o1 o2 && eq_expr t1 t2
                                          && eq_bndr O b1 b2
    | (OSch(o1,i1,s1), OSch(o2,i2,s2)) -> i1 = i2 && eq_opt_expr o1 o2 &&
                                          eq_schema s1 s2
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
         | Impl(c,e) when uvar_occurs_cond u1 c
             -> remove_occur_check e
         | Func({elt = Memb(t,a)}, b) when uvar_occurs u1 t
           -> remove_occur_check (Pos.none (Func(a,b)))
         | Func({elt = Rest(a,c)}, b) when uvar_occurs_cond u1 c
           -> remove_occur_check (Pos.none (Func(a,b)))
         | _ -> b (* NOTE #48: more cases are possible *)
       in
       let e2 = remove_occur_check e2 in
       if uvar_occurs u1 e2 then false else (uvar_set u1 e2; true)
    | (_             , UVar(_,u2)    ) when not strict ->
       let rec remove_occur_check : type a. a ex loc -> a ex loc = fun b ->
         let b = Norm.whnf b in
         match b.elt with
         | Rest(e,c) when uvar_occurs_cond u2 c
             -> remove_occur_check e
         | Memb(t,a) when uvar_occurs u2 t
           -> remove_occur_check a
         | Func({elt = Impl(c,a)}, b) when uvar_occurs_cond u2 c
           ->
            remove_occur_check (Pos.none (Func(a,b)))
         | _ -> b (* NOTE #48: more cases are possible *)
       in
       let e1 = remove_occur_check e1 in
       if uvar_occurs u2 e1 then false else (uvar_set u2 e1; true)
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
