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
                    ('a,'b) bndr -> bool }

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

(* Comparison function with unification variable instantiation. *)
let {eq_expr; eq_bndr} =
  let c = ref (-1) in
  let new_itag : type a. a sort -> a ex = fun s -> incr c; ITag(s,!c) in

  let rec eq_expr : type a. oracle -> bool -> a ex loc -> a ex loc -> bool =
    fun oracle strict e1 e2 ->
    let eq_expr e1 e2 = eq_expr oracle strict e1 e2 in
    let eq_bndr b1 b2 = eq_bndr oracle strict b1 b2 in
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
    (** bind_args and immitage: two functions for higher-order unification *)
    let bind_args : type a b. a sort -> (a -> b) args -> b ex loc -> a ex loc =
      fun sa args b ->
        let b' : b box =
          let mapper : type a. recall -> a ex loc -> a box = fun {default} e ->
            let (s',e) = Ast.sort e in
            let rec fn : type b. b args -> a box = function
              | Nil -> raise Not_found
              | Cns(s,v,a,args) ->
                 let v = box_apply Pos.none (box_of_var v) in
                 match eq_sort s s' with
                 | Eq.Eq -> if eq_expr e a then v else fn args
                 | _ -> fn args
            in
            try fn args
            with Not_found -> default e
         in
         map ~mapper:{mapper} b
       in
       let rec blam : type a. a sort -> (a -> b) args -> a box =
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
    | (HApp _        , _             ) when not strict && flexible e1 ->
       immitate e1 e2 && eq_expr e1 e2
    | (_             , HApp _        ) when not strict && flexible e2 ->
       immitate e2 e1 && eq_expr e1 e2
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
    | (Dumm(_)       , Dumm(_)       ) -> false
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

  in

  let compare_chrono = Chrono.create "compare" in

  let eq_expr : type a. ?oracle:oracle -> ?strict:bool ->
                          a ex loc -> a ex loc -> bool =
    fun ?(oracle=default_oracle) ?(strict=true) e1 e2 ->
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
    fun ?(oracle=default_oracle) ?(strict=true) s1 b1 b2 ->
      c := -1; (* Reset. *)
      Chrono.add_time compare_chrono
        (Timed.pure_test (eq_bndr oracle strict s1 b1)) b2
  in

  {eq_expr; eq_bndr}

type hash =
  { hash_expr     : 'a. 'a ex loc -> int
  ; hash_bndr     : 'a 'b. 'a sort -> ('a,'b) bndr -> int
  ; hash_ombinder : 'a. (o ex, 'a ex loc) mbinder -> int
  ; hash_vwit     : vwit -> int
  ; hash_qwit     : 'a. 'a qwit -> int
  ; hash_owit     : owit -> int
  ; hash_swit     : swit -> int
  ; hash_cwit     : schema -> int
  }

(* hash function with unification variable instantiation. *)
let {hash_expr; hash_bndr; hash_ombinder; hash_vwit
    ; hash_qwit; hash_owit; hash_swit; hash_cwit} =
  let c = ref (-1) in
  let new_itag : type a. a sort -> a ex = fun s -> incr c; ITag(s,!c) in
  let hash : type a. a -> int = Hashtbl.hash in
  let mix x y = ((y lsl 17) - x) lxor ((x lsr 7) - y) in
  let mix3 x y z = mix x (mix y z) in
  let khash1 k x = mix (hash k) x in
  let khash2 k x y = mix (hash k) (mix x y) in
  let khash3 k x y z = mix (mix (hash k) x) (mix y z) in
  let rec hash_expr : type a. a ex loc -> int =
    fun e ->
    let hash_cond = function
      | Equiv(t,b,u) -> khash3 `Equiv (hash_expr t) (hash b) (hash_expr u)
      | Posit(o)     -> hash (`Posit(hash_expr o))
      | NoBox(v)     -> hash (`NoBox(hash_expr v))
    in
    let e = Norm.whnf e in
    match e.elt with
    | HDef(_,d)   -> d.expr_hash
    | VDef(d)     -> d.value_hash
    | Valu(v)     -> hash_expr v
    | Coer(_,e,_) -> hash_expr e
    | Such(_,_,r) -> hash_expr (bseq_dummy r.binder)
    | Vari(_,x)   -> khash1 `Vari (Bindlib.hash_var x)
    | HFun(s,_,b) -> khash1 `HFun (hash_bndr s b)
    | HApp(s,f,a) -> khash3 `HApp (hash_sort s) (hash_expr f) (hash_expr a)
    | Func(a,b)   -> khash2 `Func (hash_expr a) (hash_expr b)
    | DSum(m)     -> khash1 `DSum (A.hash (fun (_,e) -> hash_expr e) m)
    | Prod(m)     -> khash1 `Prod (A.hash (fun (_,e) -> hash_expr e) m)
    | Univ(s,b)   -> khash2 `Univ (hash_sort s) (hash_bndr s b)
    | Exis(s,b)   -> khash2 `Exit (hash_sort s) (hash_bndr s b)
    | FixM(o,b)   -> khash2 `FixM (hash_expr o) (hash_bndr P b)
    | FixN(o,b)   -> khash2 `FixN (hash_expr o) (hash_bndr P b)
    | Memb(t,a)   -> khash2 `Memb (hash_expr t) (hash_expr a)
    | Rest(a,c)   -> khash2 `Rest (hash_expr a) (hash_cond c)
    | Impl(c,a)   -> khash2 `Impl (hash_expr a) (hash_cond c)
    (* NOTE type annotation ignored. *)
    | LAbs(_,b)   -> khash1 `LAbs (hash_bndr V b)
    | Cons(c,v)   -> khash2 `Cons (hash c.elt) (hash_expr v)
    | Reco(m)     -> khash1 `Reco (A.hash (fun (_,e) -> hash_expr e) m)
    | Scis        -> hash `Scis
    | Appl(t,u)   -> khash2 `Appl (hash_expr t) (hash_expr u)
    (* NOTE type annotation ignored. *)
    | MAbs(b)     -> khash1 `MAbs (hash_bndr S b)
    | Name(s,t)   -> khash2 `Name (hash_expr s) (hash_expr t)
    | Proj(v,l)   -> khash2 `Proj (hash l.elt) (hash_expr v)
    | Case(v,m)   -> khash2 `Case (hash_expr v)
                            (A.hash (fun (_,e) -> (hash_bndr V e)) m)
    | FixY(f,v)   -> hash (`FixY (hash_bndr V f, hash_expr v))
    | Prnt(s1)    -> khash1 `Prnt (hash s1)
    | Epsi        -> hash `Epsi
    | Push(v,s)   -> khash2 `Push (hash_expr v) (hash_expr s)
    | Fram(t,s)   -> khash2 `Fram (hash_expr t) (hash_expr s)
    | Conv        -> hash `Conv
    | Succ(o)     -> khash1 `Succ (hash_expr o)
    (* NOTE type annotations ignored. *)
    | ITag(_,i)   -> hash (`ITag(i))
    (* NOTE should not be compare dummy expressions. *)
    | Dumm(s)     -> khash1 `Dumm (hash_sort s)
    | VWit(w)     -> w.refr (); khash1 `VWit !(w.hash)
    | SWit(w)     -> w.refr (); khash1 `SWit !(w.hash)
    | UWit(w)     -> w.refr (); khash1 `UWit !(w.hash)
    | EWit(w)     -> w.refr (); khash1 `EWit !(w.hash)
    | OWMu(w)     -> w.refr (); khash1 `OWMu !(w.hash)
    | OWNu(w)     -> w.refr (); khash1 `OWNu !(w.hash)
    | OSch(i,o,w) -> w.refr (); khash3 `OSch i (hash_opt_expr o) !(w.hash)
    | UVar(i,u)   -> khash1 `UVar u.uvar_key
    (* two next cases are automatically stronger with oracle *)
    | VPtr v      -> khash1 `VPtr (hash v)
    | TPtr t      -> khash1 `TPtr (hash t)
    | Goal(s,str) -> khash2 `Goal (hash_sort s) (hash str)

  and hash_bndr : type a b. a sort -> (a,b) bndr -> int =
    fun s b ->
      let t = new_itag s in
      hash_expr (bndr_subst b t)

  and hash_ombinder : type a. (o ex, a ex loc) mbinder -> int =
    fun omb ->
      let ar = mbinder_arity omb in
      let ta = Array.init ar (fun _ -> new_itag O) in
      hash_expr (msubst omb ta)

  and hash_opt_expr = function
    | None -> hash `None
    | Some e -> khash1 `Some (hash_expr e)

  and hash_vwit : vwit -> int =
    fun (f,a,b) -> mix3 (hash_bndr V f) (hash_expr a) (hash_expr b)

  and hash_qwit : type a. a qwit -> int =
    fun (s,t,b) -> mix3 (hash_sort s) (hash_expr t) (hash_bndr s b)

  and hash_owit : owit -> int =
    fun (s,t,b) -> mix3 (hash_expr s) (hash_expr t) (hash_bndr O b)

  and hash_swit : swit -> int =
    fun (b,t) -> mix (hash_bndr S b) (hash_expr t)

  and hash_cwit : schema -> int =
    function
      | FixSch s -> khash1 `FixSch (hash s.fsch_index)
      | SubSch s -> khash1 `SubSch (hash s.ssch_index)
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

  let hash_owit = fun w ->
      c := -1; (* Reset. *)
      Chrono.add_time hash_chrono hash_owit w
  in
  { hash_expr; hash_bndr; hash_ombinder; hash_vwit
  ; hash_qwit; hash_owit; hash_swit; hash_cwit }

module VWit = struct
  type t = vwit
  let hash = hash_vwit
  let equal (f1,a1,b1) (f2,a2,b2) =
    eq_bndr V f1 f2 && eq_expr a1 a2 && eq_expr b1 b2
  let vars (f, a, b) = bndr_uvars V f @ uvars a @ uvars b
end

module QWit = struct
  type t = Q:'a qwit -> t
  let hash (Q w) = hash_qwit w
  let equal (Q (s1,t1,b1)) (Q(s2,t2,b2)) =
    match eq_sort s1 s2 with
    | Eq.Eq -> eq_expr t1 t2 && eq_bndr s1 b1 b2
    | _ -> false
  let vars (Q(s, t, b)) = bndr_uvars s b @ uvars t
end

module OWit = struct
  type t = owit
  let hash = hash_owit
  let equal (o1,a1,b1) (o2,a2,b2) =
    eq_expr o1 o2 && eq_expr a1 a2 && eq_bndr O b1 b2
  let vars (o, a, b) = uvars o @ uvars a @ bndr_uvars O b
end

module SWit = struct
  type t = swit
  let hash = hash_swit
  let equal (b1,a1) (b2,a2) = eq_bndr S b1 b2 && eq_expr a1 a2
  let vars (b, a) = uvars a @ bndr_uvars S b
end

module CWit = struct
  type t = schema
  let hash = hash_cwit
  let equal s1 s2 =
    (match (s1, s2) with
     | (FixSch s1, FixSch s2) -> s1.fsch_index = s2.fsch_index
     | (SubSch s1, SubSch s2) -> s1.ssch_index = s2.ssch_index
     | (_        , _        ) -> false)
  let vars s =
    (match s with
     | FixSch s ->
        let (b, mb) = s.fsch_judge in
        let (_, mb) = unmbind (mk_free O) mb in
        bndr_uvars V b @ uvars mb
     | SubSch s ->
        let mb = s.ssch_judge in
        let (_, (e1,e2)) = unmbind (mk_free O) mb in
        uvars e1 @ uvars e2)
end

let is_in : type a. a ex loc -> a ex loc list -> bool = fun e1 es ->
  List.exists (fun e2 -> eq_expr e1 e2) es
