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
  match !(u.uvar_val) with
  | Set   _     -> assert false
  | Unset hooks ->
     Timed.(u.uvar_val := Set e);
     List.iter (fun f -> f ()) hooks

let uvar_hook : type a. a uvar -> (unit -> unit) -> unit = fun u f ->
   match !(u.uvar_val) with
  | Set   _     -> ()
  | Unset hooks ->
     Timed.(u.uvar_val := Unset (f::hooks))

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
    | (VWit(w1)      , VWit(w2)      ) -> w1.valu == w2.valu
    | (SWit(_,w1)    , SWit(_,w2)    ) -> w1 == w2 ||
                                            (let (f1,a1) = w1 in
                                             let (f2,a2) = w2 in
                                             eq_bndr S f1 f2 && eq_expr a1 a2)
    | (UWit(w1)      , UWit(w2)      ) -> w1.valu == w2.valu
    | (EWit(w1)      , EWit(w2)      ) -> w1.valu == w2.valu
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

type hash =
  { hash_expr     : 'a. 'a ex loc -> int
  ; hash_bndr     : 'a 'b. 'a sort -> ('a,'b) bndr -> int
  ; hash_ombinder : 'a. (o ex, 'a ex loc) mbinder -> int
  ; hash_vwit     : vwit -> int
  ; hash_qwit     : 'a. 'a qwit -> int
  }

(* hash function with unification variable instantiation. *)
let {hash_expr; hash_bndr; hash_ombinder; hash_vwit; hash_qwit} =
  let c = ref (-1) in
  let new_itag : type a. a sort -> a ex = fun s -> incr c; ITag(s,!c) in
  let hash : type a. a -> int = Hashtbl.hash in

  let rec hash_expr : type a. a ex loc -> int =
    fun e ->
    let hash_cond = function
      | Equiv(t,b,u) -> hash (`Equiv(hash_expr t, b, hash_expr u))
      | Posit(o)     -> hash (`Posit(hash_expr o))
      | NoBox(v)     -> hash (`NoBox(hash_expr v))
    in
    let e = Norm.whnf e in
    match e.elt with
    | HDef(_,d)   -> hash_expr d.expr_def
    | VDef(d)     -> hash_expr (Erase.to_valu d.value_eval)
    | Valu(v)     -> hash_expr v
    | Coer(_,e,_) -> hash_expr e
    | Such(_,_,r) -> hash_expr (bseq_dummy r.binder)
    | Vari(_,x)   -> hash (`Vari (Bindlib.hash_var x))
    | HFun(s,_,b) -> hash (`HFun (hash_bndr s b))
    | HApp(s,f,a) -> hash (`HApp (hash_sort s, hash_expr f, hash_expr a))
    | Func(a,b)   -> hash (`Func (hash_expr a, hash_expr b))
    | DSum(m)     -> hash (`DSum (A.hash (fun (_,e) -> hash_expr e) m))
    | Prod(m)     -> hash (`Prod (A.hash (fun (_,e) -> hash_expr e) m))
    | Univ(s,b)   -> hash (`Univ (hash_sort s, hash_bndr s b))
    | Exis(s,b)   -> hash (`Exit (hash_sort s, hash_bndr s b))
    | FixM(o,b)   -> hash (`FixM (hash_expr o, hash_bndr P b))
    | FixN(o,b)   -> hash (`FixN (hash_expr o, hash_bndr P b))
    | Memb(t,a)   -> hash (`Memb (hash_expr t, hash_expr a))
    | Rest(a,c)   -> hash (`Rest (hash_expr a, hash_cond c))
    | Impl(c,a)   -> hash (`Impl (hash_expr a, hash_cond c))
    (* NOTE type annotation ignored. *)
    | LAbs(_,b)   -> hash (`LAbs (hash_bndr V b))
    | Cons(c,v)   -> hash (`Cons (c.elt, hash_expr v))
    | Reco(m)     -> hash (`Reco (A.hash (fun (_,e) -> hash_expr e) m))
    | Scis        -> hash (`Scis)
    | Appl(t,u)   -> hash (`Appl (hash_expr t, hash_expr u))
    (* NOTE type annotation ignored. *)
    | MAbs(b)     -> hash (`MAbs (hash_bndr S b))
    | Name(s,t)   -> hash (`Name (hash_expr s, hash_expr t))
    | Proj(v,l)   -> hash (`Proj (l.elt, hash_expr v))
    | Case(v,m)   -> hash (`Case (hash_expr v, A.hash (fun (_,e) -> (hash_bndr V e)) m))
    | FixY(f,v)   -> hash (`FixY (hash_bndr V f, hash_expr v))
    | Prnt(s1)    -> hash (`Prnt (s1))
    | Epsi        -> hash (`Epsi)
    | Push(v,s)   -> hash (`Push(hash_expr v, hash_expr s))
    | Fram(t,s)   -> hash (`Fram(hash_expr t, hash_expr s))
    | Conv        -> hash (`Conv)
    | Succ(o)     -> hash (`Succ (hash_expr o))
    (* NOTE type annotations ignored. *)
    | ITag(_,i)   -> hash (`ITag(i))
    (* NOTE should not be compare dummy expressions. *)
    | Dumm        -> hash (`Dumm)
    | VWit(w)     -> w.refr (); hash (`VWit !(w.hash))
    | SWit(i,w)   -> hash (`SWit(i))
    | UWit(w)     -> w.refr (); hash (`UWit !(w.hash))
    | EWit(w)     -> w.refr (); hash (`EWit !(w.hash))
    | OWMu(i,w)   -> hash (`OWMu(i))
    | OWNu(i,w)   -> hash (`OWNu(i))
    | OSch(i,w)   -> hash (`OSch(i))
    | UVar(i,u)   -> hash (`UVar(u.uvar_key))
    (* two next cases are automatically stronger with oracle *)
    | VPtr v      -> hash (`VPtr(v))
    | TPtr t      -> hash (`TPtr(t))
    | Goal(s,str) -> hash (`Goal(hash_sort s, str))

  and hash_bndr : type a b. a sort -> (a,b) bndr -> int =
    fun s b ->
      let t = new_itag s in
      hash_expr (bndr_subst b t)

  and hash_ombinder : type a. (o ex, a ex loc) mbinder -> int =
    fun omb ->
      let ar = mbinder_arity omb in
      let ta = Array.init ar (fun _ -> new_itag O) in
      hash_expr (msubst omb ta)

  and hash_vwit : vwit -> int =
    fun (f,a,b) -> hash (hash_bndr V f, hash_expr a, hash_expr b)

  and hash_qwit : type a. a qwit -> int =
    fun (s,t,b) -> hash (hash_sort s, hash_expr t, hash_bndr s b)
  in

  let hash_chrono = Chrono.create "hash" in

  let hash_expr : type a. a ex loc -> int =
    fun e ->
      c := -1; (* Reset. *)
      Chrono.add_time hash_chrono hash_expr e
  in

  let hash_bndr : type a b. a sort -> (a,b) bndr -> int =
    fun s b ->
      c := -1; (* Reset. *)
      Chrono.add_time hash_chrono (hash_bndr s) b
  in

  let hash_ombinder : type a. (o ex, a ex loc) mbinder -> int =
    fun omb ->
      c := -1; (* Reset. *)
      Chrono.add_time hash_chrono hash_ombinder omb
  in

  let hash_vwit = fun w ->
      c := -1; (* Reset. *)
      Chrono.add_time hash_chrono hash_vwit w
  in

  let hash_qwit = fun w ->
      c := -1; (* Reset. *)
      Chrono.add_time hash_chrono hash_qwit w
  in
  {hash_expr; hash_bndr; hash_ombinder; hash_vwit; hash_qwit}

module VWit = struct
  type t = vwit
  let hash = hash_vwit
  let equal (f1,a1,b1) (f2,a2,b2) =
    eq_bndr ~strict:true V f1 f2
    && eq_expr ~strict:true a1 a2
    && eq_expr ~strict:true b1 b2
  let vars (f, a, b) = bndr_uvars f @ uvars a @ uvars b
end

module QWit = struct
  type t = Q:'a qwit -> t
  let hash (Q w) = hash_qwit w
  let equal (Q (s1,t1,b1)) (Q(s2,t2,b2)) =
    match eq_sort s1 s2 with
    | Eq.Eq -> eq_expr ~strict:true t1 t2
               && eq_bndr ~strict:true s1 b1 b2
    | _ -> false
  let vars (Q(_, t, b)) = bndr_uvars b @ uvars t
end

let is_in : type a. a ex loc -> a ex loc list -> bool = fun e1 es ->
  List.exists (fun e2 -> eq_expr ~strict:true e1 e2) es
