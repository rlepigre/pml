open Bindlib
open Position
open Util
open Ast

type e_valu =
  | VVari of e_valu variable
  | VLAbs of (e_valu, e_term) binder
  | VCons of string * e_valu
  | VReco of e_valu M.t
  | VScis
and  e_term =
  | TVari of e_term variable
  | TValu of e_valu
  | TAppl of e_term * e_term
  | TMAbs of (e_stac, e_term) binder
  | TName of e_stac * e_term
  | TProj of e_valu * string
  | TCase of e_valu * (e_valu, e_term) binder M.t
  | TFixY of e_term * e_valu
and  e_stac =
  | SVari of e_stac variable
  | SEpsi
  | SPush of e_valu * e_stac
  | SFram of e_term * e_stac

type proc = e_term * e_stac

exception Erasure_error of string
let erasure_error : type a. string -> a =  fun msg -> raise (Erasure_error msg)

let rec valu_erasure : valu -> e_valu = fun v ->
  match (v.elt : v ex) with
  | Vari(x)   -> VVari(copy_var x (name_of x) (fun x -> VVari(x)))
  | HApp(_,_) -> erasure_error "not a normalisation value"
  | LAbs(_,b) -> assert false
  | Cons(c,v) -> VCons(c.elt, valu_erasure v)
  | Reco(m)   -> VReco(M.map (fun (_,v) -> valu_erasure v) m)
  | Scis      -> VScis
  | VTyp(v,_) -> valu_erasure v
  | VLam(f)   -> valu_erasure (lsubst f Dumm)
  | ITag(_)   -> erasure_error "a tag cannot be erased"
  | Dumm      -> erasure_error "a dummy value cannot be erased"
  | VWit(_)   -> erasure_error "a witness cannot be erased"
  | UWit(_)   -> erasure_error "a witness cannot be erased"
  | EWit(_)   -> erasure_error "a witness cannot be erased"
  | UVar(r)   ->
      begin
        match !r with
        | None   -> erasure_error "a unification variable cannot be erased"
        | Some v -> valu_erasure v
      end
 
(*
exception Runtime_error of string
let runtime_error : type a. string -> a = fun msg -> raise (Runtime_error msg)

let step : proc -> proc option = function
  | (Valu(v)          , Epsi      ) -> None
  | (Appl(t,u)        , pi        ) -> Some (u, Fram(t,pi))
  | (Valu(v)          , Fram(t,pi)) -> Some (t, Push(v,pi))
  | (Valu(LAbs(_,b))  , Push(v,pi)) -> Some (subst b v, pi)
  | (MAbs(b)          , pi        ) -> Some (subst b pi, pi)
  | (Name(pi,t)       , _         ) -> Some (t, pi)
  | (Proj(Reco(m),l)  , pi        ) ->
      begin
        try Some (Valu(M.find l m), pi)
        with Not_found -> runtime_error "Unknown record field"
      end
  | (Case(Cons(c,v),m), pi        ) ->
      begin
        try Some (subst (snd (M.find c m)) v, pi)
        with Not_found -> runtime_error "Unknown constructor"
      end
  | (FixY(t,v)        , pi        ) -> let f = fun x -> FixY(t,x) in
                                       let b = binder_from_fun "x" f in
                                       Some (t, Push(LAbs(None,b),Push(v,pi)))
  (* Runtime errors. *)
  | (Proj(_)          , _         ) -> runtime_error "invalid projection"
  | (Case(_,_)        , _         ) -> runtime_error "invalid case analysis"
  | (Vari(_)          , _         ) -> runtime_error "free term variable"
  | (Valu(_)          , _         ) -> runtime_error "free stack variable"
  | (HApp(_,_)        , _         ) -> runtime_error "higher-order"

let rec steps : proc -> proc = fun p ->
  match step p with
  | None   -> p
  | Some p -> steps p

let eval : term -> valu = fun t ->
  match steps (t, Epsi) with
  | (Valu v, Epsi) -> v
  | _              -> runtime_error "unexpected error"
  *)
