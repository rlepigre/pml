(** Expression comparing and unification. *)

open Bindlib
open Sorts
open Pos
open Ast
open Output
open Print
open ExprInfo

(* Log functions registration. *)
let log_equ = Log.register 'c' (Some "cmp") "comparing informations"
let log_equ = Log.(log_equ.p)

let log_uni = Log.register 'u' (Some "uni") "unification informations"
let log_uni = Log.(log_uni.p)

(* Setting a unification variable. *)
let uvar_set : type a. a uvar -> a ex loc -> unit = fun u e ->
  log_uni "?%i ← %a" u.uvar_key Print.ex e;
  assert(!(u.uvar_val) = None);
  Timed.(u.uvar_val := Some e)

(* Unification variable equality test. *)
let uvar_eq : type a. a uvar -> a uvar -> bool =
  fun u v -> u.uvar_key == v.uvar_key

type uvar_fun = { f : 'a. 'a sort -> 'a uvar -> unit }

let uvar_iter : type a. uvar_fun -> a ex loc -> unit = fun f e ->
  let not_closed b = not (Bindlib.binder_closed (snd b)) in
  let adone = Ahash.create 101 in
  let test_done e =
    if Ahash.mem adone (Obj.repr e) then true
    else (
      Ahash.add adone (Obj.repr e) ();
      false)
  in
  let rec uvar_iter : type a. a ex loc -> unit = fun e ->
    let uvar_iter_cond f c =
      match c with
      | Equiv(t,_,u) -> uvar_iter t; uvar_iter u
      | Posit(o)     -> uvar_iter o
    in
    let buvar_iter b = if not_closed b then uvar_iter (bndr_subst b Dumm) in
    let e = Norm.whnf e in
    if not (test_done e) then match e.elt with
    | Vari(_)     -> ()
    | HFun(_,_,b) -> buvar_iter b
    | HApp(_,a,b) -> uvar_iter a; uvar_iter b
    | HDef(_)     -> () (* NOTE no unification variable in definition. *)
    | Func(a,b)   -> uvar_iter a; uvar_iter b
    | Prod(m)     -> M.iter (fun _ (_,a) -> uvar_iter a) m
    | DSum(m)     -> M.iter (fun _ (_,a) -> uvar_iter a) m
    | Univ(_,b)   -> buvar_iter b
    | Exis(_,b)   -> buvar_iter b
    | FixM(o,b)   -> uvar_iter o; buvar_iter b
    | FixN(o,b)   -> uvar_iter o; buvar_iter b
    | Memb(t,a)   -> uvar_iter t; uvar_iter a
    | Rest(a,c)   -> uvar_iter a; uvar_iter_cond f c
    | Impl(c,a)   -> uvar_iter_cond f c; uvar_iter a
    (* NOTE type annotation ignored. *)
    | LAbs(_,b)   -> buvar_iter b
    | Cons(_,v)   -> uvar_iter v
    | Reco(m)     -> M.iter (fun _ (_,a) -> uvar_iter a) m
    | Scis        -> ()
    | VDef(_)     -> () (* NOTE no unification variable in definition. *)
    | Valu(v)     -> uvar_iter v
    | Appl(t,u)   -> uvar_iter t; uvar_iter u
    (* NOTE type annotation ignored. *)
    | MAbs(b)     -> buvar_iter b
    | Name(s,t)   -> uvar_iter s; uvar_iter t
    | Proj(v,_)   -> uvar_iter v
    | Case(v,m)   -> let fn _ (_,b) = buvar_iter b in
                     uvar_iter v; M.iter fn m
    | FixY(t,v)   -> uvar_iter t; uvar_iter v
    | Epsi        -> ()
    | Push(v,s)   -> uvar_iter v; uvar_iter s
    | Fram(t,s)   -> uvar_iter t; uvar_iter s
    | Conv        -> ()
    | Succ(o)     -> uvar_iter o
    (* NOTE type annotations ignored. *)
    | VTyp(v,_)   -> uvar_iter v
    | TTyp(t,_)   -> uvar_iter t
    | VLam(_,b)   -> buvar_iter b
    | TLam(_,b)   -> buvar_iter b
    | ITag(_)     -> ()
    | Dumm        -> ()
    | VWit(b,a,c) -> buvar_iter b; uvar_iter a; uvar_iter c
    | SWit(b,a)   -> buvar_iter b; uvar_iter a
    | UWit(_,t,b) -> uvar_iter t; buvar_iter b
    | EWit(_,t,b) -> uvar_iter t; buvar_iter b
    | OWit(o,i,s) -> let (_,(t,k)) = Bindlib.unmbind mk_free s.sch_judge in
                     uvar_iter o; uvar_iter t; uvar_iter k
    | UVar(s,u)   -> f.f s u
  in uvar_iter e

type s_elt = U : 'a sort * 'a uvar -> s_elt

let uvars : type a. a ex loc -> s_elt list = fun e ->
  let uvars = ref [] in
  let f s u =
    let p (U(_,v)) = v.uvar_key == u.uvar_key in
    if not (List.exists p !uvars) then uvars := (U(s,u)) :: !uvars
  in
  uvar_iter {f} e; !uvars

let uvar_occurs : type a b. a uvar -> b ex loc -> bool = fun u e ->
  let f _ v =
    if v.uvar_key == u.uvar_key then
      begin
        log_equ "Occur check on %d" u.uvar_key;
        raise Exit
      end
  in
  try uvar_iter {f} e; false with Exit -> true

let full_eq = ref false

exception DontKnow
type oracle = { eq_val :v ex loc -> v ex loc -> bool }

let default_oracle = {
    eq_val = fun _ _ -> raise DontKnow
  }

type eq =
  { eq_expr : 'a. ?oracle:oracle -> ?strict:bool ->
                'a ex loc -> 'a ex loc -> bool
  ; eq_bndr : 'a 'b. ?oracle:oracle -> ?strict:bool -> 'a sort ->
                ('a,'b) bndr -> ('a,'b) bndr -> bool
  }

(* Comparison function with unification variable instantiation. *)
let {eq_expr; eq_bndr} =
  let c = ref (-1) in
  let new_itag : type a. a sort -> a ex = fun s -> incr c; ITag(s,!c) in

  let rec eq_expr : type a. oracle -> bool -> a ex loc -> a ex loc -> bool =
    fun oracle strict e1 e2 ->
    let eq_expr e1 e2 = eq_expr oracle strict e1 e2 in
    let eq_bndr b1 b2 = eq_bndr oracle strict b1 b2 in
    let e1 = Norm.whnf e1 in
    let e2 = Norm.whnf e2 in
    if e1 == e2 then true else (
    if !full_eq then log_equ "comparing %a and %a" Print.ex e1 Print.ex e2;
    match (e1.elt, e2.elt) with
    | (Vari(x1)      , Vari(x2)      ) ->
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
        M.equal (fun (_,a1) (_,a2) -> eq_expr a1 a2) m1 m2
    | (Prod(m1)      , Prod(m2)      ) ->
        M.equal (fun (_,a1) (_,a2) -> eq_expr a1 a2) m1 m2
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
            | (_              , _              ) ->
                false
          end
    (* NOTE type annotation ignored. *)
    | (LAbs(_,b1)   , LAbs(_,b2)    )  -> eq_bndr V b1 b2
    | (Cons(c1,v1)   , Cons(c2,v2)   ) -> c1.elt = c2.elt && eq_expr v1 v2
    | (Reco(m1)      , Reco(m2)      ) ->
        M.equal (fun (_,v1) (_,v2) -> eq_expr v1 v2) m1 m2
    | (Scis          , Scis          ) -> true
    | (VDef(d1)      , VDef(d2)      ) -> d1 == d2 (* FIXME ? *)
    | (Valu(v1)      , Valu(v2)      ) -> eq_expr v1 v2
    | (Appl(t1,u1)   , Appl(t2,u2)   ) -> eq_expr t1 t2 && eq_expr u1 u2
    (* NOTE type annotation ignored. *)
    | (MAbs(b1)      , MAbs(b2)      ) -> eq_bndr S b1 b2
    | (Name(s1,t1)   , Name(s2,t2)   ) -> eq_expr s1 s2 && eq_expr t1 t2
    | (Proj(v1,l1)   , Proj(v2,l2)   ) -> l1.elt = l2.elt && eq_expr v1 v2
    | (Case(v1,m1)   , Case(v2,m2)   ) ->
        let cmp (_,b1) (_,b2) = eq_bndr V b1 b2 in
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
    | (ITag(_,i1)    , ITag(_,i2)    ) -> i1 = i2
    (* NOTE should not be compare dummy expressions. *)
    | (Dumm          , Dumm          ) -> false
    | (VWit(f1,a1,b1), VWit(f2,a2,b2)) ->
        eq_bndr V f1 f2 && eq_expr a1 a2 && eq_expr b1 b2
    | (SWit(f1,a1)   , SWit(f2,a2)   ) -> eq_bndr S f1 f2 && eq_expr a1 a2
    | (UWit(s1,t1,b1), UWit(_,t2,b2) ) -> eq_bndr s1 b1 b2 && eq_expr t1 t2
    | (EWit(s1,t1,b1), EWit(_,t2,b2) ) -> eq_bndr s1 b1 b2 && eq_expr t1 t2
    | (UVar(_,u1)    , UVar(_,u2)    ) ->
       if strict then u1.uvar_key = u2.uvar_key else
         begin
           if u1.uvar_key <> u2.uvar_key then uvar_set u1 e2; (* arbitrary *)
           true
         end
    (* FIXME experimental. *)
    | (UVar(_,u1)    , Func({elt = Memb(t,a)}, b))
                   when not strict && uvar_occurs u1 t ->
       eq_expr e1 (Pos.none (Func(a,b)))
    | (UVar(_,u1)    , _             ) when not strict ->
       if uvar_occurs u1 e2 then false else (uvar_set u1 e2; true)
    | (_             , UVar(_,u2)    ) when not strict ->
       if uvar_occurs u2 e1 then false else (uvar_set u2 e1; true)
    | _                                -> false)

  and eq_bndr : type a b. oracle -> bool -> a sort ->
                            (a,b) bndr -> (a,b) bndr -> bool =
    fun oracle strict s1 b1 b2 ->
      if b1 == b2 then true else
        let t = new_itag s1 in
        eq_expr oracle strict (bndr_subst b1 t) (bndr_subst b2 t)
  in

  let eq_expr : type a. ?oracle:oracle -> ?strict:bool ->
                          a ex loc -> a ex loc -> bool =
    fun ?(oracle=default_oracle) ?(strict=false) e1 e2 ->
      c := -1; (* Reset. *)
      log_equ "trying to show %a === %a" Print.ex e1 Print.ex e2;
      let res = Timed.pure_test (eq_expr oracle strict e1) e2 in
      log_equ "we have %a %s %a"
              Print.ex e1 (if res then "=" else "≠") Print.ex e2;
      res
  in

  let eq_bndr : type a b. ?oracle:oracle -> ?strict:bool ->
                     a sort -> (a,b) bndr -> (a,b) bndr -> bool =
    fun ?(oracle=default_oracle) ?(strict=false) s1 b1 b2 ->
      c := -1; (* Reset. *)
      let res = Timed.pure_test (eq_bndr oracle strict s1 b1) b2 in
      res
  in
  {eq_expr; eq_bndr}
