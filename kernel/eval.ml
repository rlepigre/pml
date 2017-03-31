(** Evaluation in an abstract machine. *)

open Bindlib
open Pos

module A = Assoc

type e_valu =
  | VVari of e_valu var
  | VLAbs of (e_valu, e_term) binder
  | VCons of string * e_valu
  | VReco of e_valu A.t
  | VScis
and  e_term =
  | TVari of e_term var
  | TValu of e_valu
  | TAppl of e_term * e_term
  | TMAbs of (e_stac, e_term) binder
  | TName of e_stac * e_term
  | TProj of e_valu * string
  | TCase of e_valu * (e_valu, e_term) binder A.t
  | TFixY of (e_valu, e_term) binder * e_valu
and  e_stac =
  | SVari of e_stac var
  | SEpsi
  | SPush of e_valu * e_stac
  | SFram of e_term * e_stac

type e_vvar = e_valu var
type e_tvar = e_term var
type e_svar = e_stac var

type e_vbox = e_valu bindbox
type e_tbox = e_term bindbox
type e_sbox = e_stac bindbox

let mk_vvari : e_valu var -> e_valu =
  fun x -> VVari(x)

let mk_tvari : e_term var -> e_term =
  fun x -> TVari(x)

let mk_svari : e_stac var -> e_stac =
  fun x -> SVari(x)

(* Smart constructors for values. *)
let vlabs : string -> (e_vvar -> e_tbox) -> e_vbox =
  fun x f -> box_apply (fun b -> VLAbs(b)) (vbind mk_vvari x f)

let vcons : string -> e_vbox -> e_vbox =
  fun c -> box_apply (fun v -> VCons(c,v))

let vreco : e_vbox A.t -> e_vbox =
  fun m -> box_apply (fun m -> VReco(m)) (A.lift_box m)

let vscis : e_vbox =
  box VScis

(* Smart constructors for terms. *)
let tvalu : e_vbox -> e_tbox =
  box_apply (fun v -> TValu(v))

let tappl : e_tbox -> e_tbox -> e_tbox =
  box_apply2 (fun t u -> TAppl(t,u))

let tmabs : string -> (e_svar -> e_tbox) -> e_tbox =
  fun x f -> box_apply (fun b -> TMAbs(b)) (vbind mk_svari x f)

let tname : e_sbox -> e_tbox -> e_tbox =
  box_apply2 (fun s t -> TName(s,t))

let tproj : e_vbox -> string -> e_tbox =
  fun v l -> box_apply (fun v -> TProj(v,l)) v

let tcase : e_vbox -> (string * (e_vvar -> e_tbox)) A.t -> e_tbox =
  fun v m ->
    let f (x,f) = vbind mk_vvari x f in
    box_apply2 (fun v m -> TCase(v,m)) v (A.map_box f m)

let tfixy : string -> (e_vvar -> e_tbox) -> e_vbox -> e_tbox =
  fun x f -> box_apply2 (fun b v -> TFixY(b,v)) (vbind mk_vvari x f)

(* Smart constructors for stacks. *)
let sepsi : e_sbox =
  box SEpsi

let spush : e_vbox -> e_sbox -> e_sbox =
  box_apply2 (fun v s -> SPush(v,s))

let sfram : e_tbox -> e_sbox -> e_sbox =
  box_apply2 (fun t s -> SFram(t,s))

(* Reduction. *)
type proc = e_term * e_stac

exception Runtime_error of string
let runtime_error : type a. string -> a =
  fun msg -> raise (Runtime_error msg)

let step : proc -> proc option = function
  | (TValu(v)          , SEpsi      ) -> None
  | (TAppl(t,u)        , pi         ) -> Some (u, SFram(t,pi))
  | (TValu(v)          , SFram(t,pi)) -> Some (t, SPush(v,pi))
  | (TValu(VLAbs(b))   , SPush(v,pi)) -> Some (subst b v, pi)
  | (TMAbs(b)          , pi         ) -> Some (subst b pi, pi)
  | (TName(pi,t)       , _          ) -> Some (t, pi)
  | (TProj(VReco(m),l) , pi         ) ->
      begin
        try Some (TValu(A.find l m), pi)
        with Not_found -> runtime_error "Unknown record field"
      end
  | (TCase(VCons(c,v),m), pi        ) ->
      begin
        try Some (subst (A.find c m) v, pi)
        with Not_found -> runtime_error "Unknown constructor"
      end
  | (TFixY(b,v)        , pi         ) ->
      begin
        let f = binder_from_fun "x" (fun x -> TFixY(b,x)) in
        Some (TValu(VLAbs(b)), SPush(VLAbs(f),SPush(v,pi)))
      end
  (* Runtime errors. *)
  | (TProj(_)          , _          ) -> runtime_error "invalid projection"
  | (TCase(_,_)        , _          ) -> runtime_error "invalid case analysis"
  | (TVari(_)          , _          ) -> runtime_error "free term variable"
  | (TValu(_)          , _          ) -> runtime_error "free stack variable"

let rec steps : proc -> proc = fun p ->
  match step p with
  | None   -> p
  | Some p -> steps p

let eval : e_term -> e_valu = fun t ->
  match steps (t, SEpsi) with
  | (TValu v, SEpsi) -> v
  | (_      , _    ) -> runtime_error "unexpected error"
