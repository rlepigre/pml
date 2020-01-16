(** Expression comparing and unification. *)

open Bindlib
open Eq
open Sorts
open Pos
open Ast
open Output
open Print
open Uvars
open Mapper

(* Log functions registration. *)
let log_equ = Log.register 'c' (Some "cmp") "comparing informations"
let log_equ = Log.(log_equ.p)

(* Setting a unification variable. (not in uvars.ml: needs print) *)
let uvar_set : type a. a uvar -> a ex loc -> unit = fun u e ->
  log_uni "?%i ← %a" u.uvar_key Print.ex e;
  match !(u.uvar_val) with
  | Set   _     -> assert false
  | Unset hooks -> UTimed.(u.uvar_val := Set e);
                   List.iter (fun f -> f ()) hooks

(* adds a hook to a unification variables, currently only used for
   epsilon. May be soon for pool updates *)
let uvar_hook : type a. a uvar -> (unit -> unit) -> unit = fun u f ->
   match !(u.uvar_val) with
  | Set   _     -> ()
  | Unset hooks -> UTimed.(u.uvar_val := Unset (f::hooks))

(* trigger more detailed printing *)
let full_eq = ref false

(* an oracle allows (optionally) to call the pool to use the equational
   hypothesis to decide equality, so we share the code between a syntactic
   and a more semantical equality *)

(* oracle provide code for testing equality on valu and terms and can
   raise DontKnow *)
exception DontKnow
type oracle = { eq_val :v ex loc -> v ex loc -> bool;
                eq_trm :t ex loc -> t ex loc -> bool }

(* the default oracle *)
let default_oracle = {
    eq_val = (fun _ _ -> raise DontKnow);
    eq_trm = (fun _ _ -> raise DontKnow)
  }

(* for texhnial reason due to OCaml typing, equalities
   are in a record *)
type eq =
  { eq_expr     : 'a. ?oracle:oracle -> ?strict:bool ->
                    'a ex loc -> 'a ex loc -> bool
  ; eq_bndr     : 'a 'b. ?oracle:oracle -> ?strict:bool -> 'a sort ->
                    ('a,'b) bndr ->
                    ('a,'b) bndr -> bool }

(* test if the head of higher ordre application is a unification
   variable. This are called flexible terms when doing higher-order
   unification *)
let rec flexible : type a. a ex loc -> bool = fun e ->
  let e = Norm.whnf e in
  match e.elt with
  | UVar _ -> true
  | HApp(s,f,_) -> flexible f
  | _ -> false

(** A type to store the arguments for higher-order unification *)
type 'a args =
  | Nil : ('a -> 'a) args
  | Cns : 'a sort * 'a var * 'a ex loc * ('b -> 'c) args ->
          (('a -> 'b) -> 'c) args

(* Comparison function with unification variable instantiation,
   and optionnaly using the pool oracle. *)
let {eq_expr; eq_bndr} =

  let rec eq_expr : type a. oracle -> bool -> a ex loc -> a ex loc -> bool =
    fun oracle strict e1 e2 ->
    let eq_expr  e1 e2 = eq_expr oracle strict e1 e2 in
    let eq_bndr  b1 b2 = eq_bndr oracle strict b1 b2 in
    let eq_fix_schema sch1 sch2 =
      sch1.fsch_index = sch2.fsch_index
    in
    let eq_sub_schema sch1 sch2 =
      sch1.ssch_index = sch2.ssch_index
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
    let rec eq_args
            : type a b c.(a, b) fix_args -> (a, c) fix_args -> (b,c) Eq.t
      = fun l1 l2 ->
      match (l1, l2) with
      | (Nil      , Nil      ) -> Eq
      | (Cns(a,l1), Cns(b,l2)) ->
         begin
           match eq_args l1 l2 with
           | Eq  -> if eq_expr a b then Eq else NEq
           | NEq -> NEq
         end
      | _                      -> NEq
    in
    (** bind_args and immitate: two functions for higher-order unification *)
    (** bind_args sa args b, uses our ast mapper to bind all the arguments
        present in the list args in b. This is the main auxiliary function for
        immitate *)
    let bind_args : type a b.a sort -> (a -> b) args -> b ex loc -> a ex loc =
      fun sa args b ->
        let b' : b ebox =
          let mapper : type a. recall -> a ex loc -> a ebox =
            fun {default} e ->
              let (s',e) = Ast.sort e in
              let rec fn : type b. b args -> a ebox = function
                | Nil -> raise Not_found
                | Cns(s,v,a,args) ->
                   let v = box_apply Pos.none (box_var v) in
                   match eq_sort s s' with
                   | Eq.Eq -> if eq_expr e a then v else fn args
                   | _ -> fn args
              in
              try fn args
              with Not_found -> default e
         in
         map ~mapper:{mapper} b
       in
       (** last we build the lambda (HFun) from the list *)
       let rec blam : type a. a sort -> (a -> b) args -> a ebox =
         fun sa args ->
           match args with
           | Nil -> b'
           | Cns(sb,w,_,args) ->
              (* b = sa -> b' *)
              match sa with
              | F(_,s) ->
                 let t = blam s args in
                 box_apply (fun x -> Pos.none (HFun(sb,s,(None,x))))
                           (bind_var w t)
              | _ -> .
       in
       unbox (blam sa args)
   in
   (* immitate a b set the variable at the head of a to immitate b,
      using whenever possible the argument of the variable (prefers
      projection *)
   let immitate : type a. a ex loc -> a ex loc -> bool =
    fun a b ->
      let rec fn : type b. b ex loc -> (b -> a) args -> bool =
        fun f args ->
          match (Norm.whnf f).elt with
          | HApp(s,f,a) ->
             let v = new_var (mk_free s) "x" in
             fn f (Cns(s,v,a,args))
          | UVar(s,uv) ->
             let b = bind_args s args b in
             log_uni "projection";
             not (uvar_occurs uv b) && (uvar_set uv b; true)
          | _ -> assert false
      in
      fn a Nil
    in
    let e1 = Norm.whnf e1 in
    let e2 = Norm.whnf e2 in
    (** first physical equality *)
    if e1.elt == e2.elt then true else (
    (** second we try the oracle *)
    try
      match (Ast.sort e1, Ast.sort e2) with
      | (V, e1), (V,e2) -> oracle.eq_val e1 e2
      | (T, e1), (T,e2) -> oracle.eq_trm e1 e2
      | _ -> raise DontKnow
    with DontKnow ->
    (** third we recurse *)
    if !full_eq then log_equ "comparing %a and %a (%b)"
                             Print.ex e1 Print.ex e2 strict;
    match (e1.elt, e2.elt) with
    | (Vari(_,x1)    , Vari(_,x2)    ) ->
       Bindlib.eq_vars x1 x2
    | (HFun(s1,_,b1) , HFun(_,_,b2)  ) -> eq_bndr s1 b1 b2
    | (UVar(_,u1)    , UVar(_,u2)    ) ->
       assert (u1.uvar_key >= 0);
       if strict && u2.uvar_key >= 0 then u1.uvar_key = u2.uvar_key else
         begin
           if u1.uvar_key <> u2.uvar_key then
             if not (uvar_occurs u2 e1) then (uvar_set u2 e1; true)
             else false
           else true
         end
    | (UVar(_,u1)    , _             ) when not strict ->
       assert (u1.uvar_key >= 0);
       let rec remove_occur_check : type a. a ex loc -> a ex loc = fun b ->
         let b = Norm.whnf b in
         match b.elt with
         | Impl(c,e) when uvar_occurs_rel u1 c
           -> remove_occur_check e
         | Func(tot,{elt = Memb(t,a)}, b, l) when uvar_occurs u1 t
           -> remove_occur_check (Pos.none (Func(tot,a,b,l)))
         | Func(tot,{elt = Rest(a,c)}, b, l) when uvar_occurs_rel u1 c
           -> remove_occur_check (Pos.none (Func(tot,a,b,l)))
         | _ -> b (* NOTE #48: more cases are possible *)
       in
       let e2 = remove_occur_check e2 in
       if uvar_occurs u1 e2 then false else (uvar_set u1 e2; true)
    | (_             , UVar(_,u2)    ) when not strict || u2.uvar_key < 0 ->
       let rec remove_occur_check : type a. a ex loc -> a ex loc = fun b ->
         let b = Norm.whnf b in
         match b.elt with
         | Rest(e,c) when uvar_occurs_rel u2 c ->
             remove_occur_check e
         | Memb(t,a) when uvar_occurs u2 t     ->
             remove_occur_check a
         | Func(tot,{elt = Impl(c,a)}, b, l) when uvar_occurs_rel u2 c ->
             remove_occur_check (Pos.none (Func(tot,a,b,l)))
         | _ -> b (* NOTE #48: more cases are possible *)
       in
       let e1 = remove_occur_check e1 in
       if uvar_occurs u2 e1 then false else (uvar_set u2 e1; true)
    | (HApp(s1,f1,a1), HApp(s2,f2,a2)) ->
        begin
          match eq_sort s1 s2 with
          | Eq  -> eq_expr f1 f2 && eq_expr a1 a2
          | NEq -> false
        end
        (** deal with flexible case ... NOTE: the case with
            two flexible should probably be postponed *)
        || (if not strict && flexible e1 then
              immitate e1 e2 && eq_expr e1 e2
            else if not strict && flexible e2 then
              immitate e2 e1 && eq_expr e1 e2
            else false)
    (* the other flexible cases. NOTE: we don't trust immitate and
       call eq_expr anyway.  *)
    | (HApp _        , _             ) when not strict && flexible e1 ->
       immitate e1 e2 && eq_expr e1 e2
    | (_             , HApp _        ) when not strict && flexible e2 ->
       immitate e2 e1 && eq_expr e1 e2
    | (HFun(s1,_,b1), _             ) ->
       let (v,t) = bndr_open b1 in
       eq_expr t (Pos.none (HApp(s1,e2,Pos.none (Vari(s1,v)))))
    | (_             , HFun(s2,_,b2)) ->
       let (v,t) = bndr_open b2 in
       eq_expr (Pos.none (HApp(s2,e1,Pos.none (Vari(s2,v))))) t
    | (HDef(_,d)     , _             ) -> eq_expr d.expr_def e2
    | (_             , HDef(_,d)     ) -> eq_expr e1 d.expr_def
    | (Func(t1,a1,b1,l1), Func(t2,a2,b2,l2)) ->
       (if strict then Effect.know_eq else Effect.eq) t1 t2
       && eq_expr a1 a2 && eq_expr b1 b2 && l1 = l2
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
    | (FixM(s1,o1,b1,l1), FixM(s2,o2,b2,l2)) ->
       begin
         match eq_sort s1 s2 with
         | Eq  -> eq_expr o1 o2 && eq_bndr s1 b1 b2 && eq_args l1 l2 = Eq
         | NEq -> false
       end
    | (FixN(s1,o1,b1,l1), FixN(s2,o2,b2,l2)) ->
       begin
         match eq_sort s1 s2 with
         | Eq  -> eq_expr o1 o2 && eq_bndr s1 b1 b2 && eq_args l1 l2 = Eq
         | NEq -> false
       end
    | (Memb(t1,a1)   , Memb(t2,a2)   ) -> eq_expr t1 t2 && eq_expr a1 a2
    | (Rest(a1,c1)   , Rest(a2,c2)   ) ->
        eq_expr a1 a2 &&
          begin
            match (c1, c2) with
            | (Equiv(t1,b1,u1), Equiv(t2,b2,u2)) ->
                b1 = b2 && eq_expr t1 t2 && eq_expr u1 u2
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
            | (NoBox(v1)      , NoBox(v2)      ) ->
               eq_expr v1 v2
            | (_              , _              ) ->
                false
          end
    (* NOTE type annotation ignored. *)
    | (LAbs(_,b1,l1) , LAbs(_,b2,l2) ) -> eq_bndr V b1 b2 && l1 = l2
    | (Cons(c1,v1)   , Cons(c2,v2)   ) -> c1.elt = c2.elt && eq_expr v1 v2
    | (Reco(m1)      , Reco(m2)      ) ->
        A.equal (fun (_,v1) (_,v2) -> eq_expr v1 v2) m1 m2
    | (Scis          , Scis          ) -> true
    | (VDef(d1)      , VDef(d2)      ) when d1 == d2
                                       -> true
    | (VDef(d1)      , _             ) -> eq_expr d1.value_eras e2
    | (_             , VDef(d2)      ) -> eq_expr e1 d2.value_eras
    | (Valu(v1)      , Valu(v2)      ) -> eq_expr v1 v2
    | (Appl(t1,u1,_) , Appl(t2,u2,_) ) -> eq_expr t1 t2 && eq_expr u1 u2
    (* NOTE type annotation ignored. *)
    | (MAbs(b1)      , MAbs(b2)      ) -> eq_bndr S b1 b2
    | (Name(s1,t1)   , Name(s2,t2)   ) -> eq_expr s1 s2 && eq_expr t1 t2
    | (Proj(v1,l1)   , Proj(v2,l2)   ) -> l1.elt = l2.elt && eq_expr v1 v2
    | (Case(v1,m1)   , Case(v2,m2)   ) ->
        let cmp (_,b1) (_,b2) = eq_bndr V b1 b2 in
        eq_expr v1 v2 && A.equal cmp m1 m2
    | (FixY(f1)      , FixY(f2)      ) -> eq_bndr T f1 f2
    | (Prnt(s1)      , Prnt(s2)      ) -> s1 = s2
    | (Conv          , Conv          ) -> true
    | (Succ(o1)      , Succ(o2)      ) -> eq_expr o1 o2
    (* NOTE type annotations ignored. *)
    | (Repl(_,u1)    , _             ) -> eq_expr u1 e2
    | (_             , Repl(_,u2)    ) -> eq_expr e1 u2
    | (Delm(u1)      , _             ) -> eq_expr u1 e2
    | (_             , Delm(u2)      ) -> eq_expr e1 u2
    | (Coer(_,e1,_)  , _             ) -> eq_expr e1 e2
    | (_             , Coer(_,e2,_)  ) -> eq_expr e1 e2
    | (Such(_,_,r)   , _             ) -> eq_expr (bseq_open r.binder) e2
    | (_             , Such(_,_,r)   ) -> eq_expr e1 (bseq_open r.binder)
    | (PSet(_,_,e1)  , _             ) -> eq_expr e1 e2
    | (_             , PSet(_,_,e2)  ) -> eq_expr e1 e2
    | (VWit(w1)      , VWit(w2)      ) ->
       w1.valu == w2.valu ||
         if strict || (!(w1.vars) = [] && !(w2.vars) = [])
         then false
         else (let (f1,a1,b1) = !(w1.valu) in
               let (f2,a2,b2) = !(w2.valu) in
               eq_bndr V f1 f2 && eq_expr a1 a2 && eq_expr b1 b2)
    | (SWit(w1)      , SWit(w2)      ) ->
       !(w1.valu) == !(w2.valu) ||
         if strict || (!(w1.vars) = [] && !(w2.vars) = [])
         then false
         else (let (f1,a1) = !(w1.valu) in
               let (f2,a2) = !(w2.valu) in
               eq_bndr S f1 f2 && eq_expr a1 a2)
    | (UWit(w1)      , UWit(w2)      ) ->
       !(w1.valu) == !(w2.valu) ||
         if strict || (!(w1.vars) = [] && !(w2.vars) = [])
         then false
         else (let (s1,t1,b1) = !(w1.valu) in
               let (s2,t2,b2) = !(w2.valu) in
               match eq_sort s1 s2 with
               | Eq.Eq -> eq_expr t1 t2 && eq_bndr s1 b1 b2
               | _     -> false)
    | (EWit(w1)      , EWit(w2)      ) ->
       !(w1.valu) == !(w2.valu) ||
         if strict || (!(w1.vars) = [] && !(w2.vars) = [])
         then false
         else (let (s1,t1,b1) = !(w1.valu) in
               let (s2,t2,b2) = !(w2.valu) in
               match eq_sort s1 s2 with
               | Eq.Eq -> eq_expr t1 t2 && eq_bndr s1 b1 b2
               | _     -> false)
    | (OWMu(w1)      , OWMu(w2)      ) ->
       !(w1.valu) == !(w2.valu) ||
         if strict || (!(w1.vars) = [] && !(w2.vars) = [])
         then false
         else (let (o1,t1,b1) = !(w1.valu) in
               let (o2,t2,b2) = !(w2.valu) in
               eq_expr o1 o2 && eq_expr t1 t2
               && eq_bndr O b1 b2)
    | (OWNu(w1)      , OWNu(w2)      ) ->
       !(w1.valu) == !(w2.valu) ||
         if strict || (!(w1.vars) = [] && !(w2.vars) = [])
         then false
         else (let (o1,t1,b1) = !(w1.valu) in
               let (o2,t2,b2) = !(w2.valu) in
               eq_expr o1 o2 && eq_expr t1 t2 && eq_bndr O b1 b2)
    | (OSch(i1,o1,w1), OSch(i2,o2,w2)) ->
       i1 = i2
       && eq_opt_expr o1 o2
       && (!(w1.valu) == !(w2.valu) ||
             if strict || (!(w1.vars) = [] && !(w2.vars) = [])
             then false
             else (let s1 = !(w1.valu) in
                   let s2 = !(w2.valu) in
                   eq_schema s1 s2))
    | (ESch(s1,i1,w1), ESch(s2,i2,w2)) ->
       i1 = i2
       && (!(w1.valu) == !(w2.valu) ||
             if strict || (!(w1.vars) = [] && !(w2.vars) = [])
             then false
             else (let s1 = !(w1.valu) in
                   let s2 = !(w2.valu) in
                   eq_schema s1 s2))
    (* two next cases are automatically stronger with oracle *)
    | (VPtr v1       , VPtr v2       ) -> Ptr.VPtr.compare v1 v2 = 0
    | (TPtr t1       , TPtr t2       ) -> Ptr.Ptr.compare t1 t2 = 0
    | _                                -> false)

  and eq_bndr : type a b. oracle -> bool -> a sort ->
                            (a,b) bndr -> (a,b) bndr -> bool =
    fun oracle strict s1 (_,b1) (_,b2) ->
      if b1 == b2 then true else
        eq_binder (eq_expr oracle strict) b1 b2
  in

  let compare_chrono = Chrono.create "compare" in

  let eq_expr : type a. ?oracle:oracle -> ?strict:bool ->
                          a ex loc -> a ex loc -> bool =
    fun ?(oracle=default_oracle) ?(strict=true) e1 e2 ->
      let is_oracle = oracle != default_oracle in
      log_equ "showing %a === %a (%b)" Print.ex e1 Print.ex e2 is_oracle;
      (*bug_msg "sizes: %i and %i" (binary_size e1) (binary_size e2);*)
      let res = Chrono.add_time compare_chrono
                  (UTimed.pure_test (eq_expr oracle strict e1)) e2 in
      log_equ "we have %a %s %a"
              Print.ex e1 (if res then "=" else "≠") Print.ex e2;
      res
  in

  let eq_bndr : type a b. ?oracle:oracle -> ?strict:bool ->
                     a sort -> (a,b) bndr -> (a,b) bndr -> bool =
    fun ?(oracle=default_oracle) ?(strict=true) s1 b1 b2 ->
      Chrono.add_time compare_chrono
        (UTimed.pure_test (eq_bndr oracle strict s1 b1)) b2
  in

  {eq_expr; eq_bndr}

let _ = feq_expr.eq <-
  fun e f -> (* fex_expr is called from print ... log must be disabled ! *)
    let save = Log.get_enabled () in
    try
      Log.set_enabled "";
      let b = eq_expr e f in
      Log.set_enabled save;
      b
    with
      e -> Log.set_enabled save; raise e

(** use eq_expr for a list membershipt test *)
let is_in : type a. a ex loc -> a ex loc list -> bool = fun e1 es ->
  List.exists (fun e2 -> eq_expr e1 e2) es

module Expr = struct
  type t = E : 'a ex loc -> t
  let equal (E e1) (E e2) =
    match Ast.sort e1, Ast.sort e2 with
    | (s1, e1), (s2, e2) ->
       match eq_sort s1 s2 with
       | Eq -> eq_expr e1 e2
       | _  -> false
  let hash (E e) = Hash.hash_expr e
end

module HExpr = Hashtbl.Make(Expr)
