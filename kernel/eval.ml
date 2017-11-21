(** Evaluation in an abstract machine. *)

open Bindlib
open Ast
open Pos

module A = Assoc

type e_vvar = e_valu Bindlib.var
type e_tvar = e_term Bindlib.var
type e_svar = e_stac Bindlib.var

type e_vbox = e_valu bindbox
type e_tbox = e_term bindbox
type e_sbox = e_stac bindbox

let mk_vvari : e_valu Bindlib.var -> e_valu =
  fun x -> VVari(x)

let mk_tvari : e_term Bindlib.var -> e_term =
  fun x -> TVari(x)

let mk_svari : e_stac Bindlib.var -> e_stac =
  fun x -> SVari(x)

(* Smart constructors for values. *)
let vlabs : string -> (e_vvar -> e_tbox) -> e_vbox =
  fun x f -> box_apply (fun b -> VLAbs(b)) (Bindlib.vbind mk_vvari x f)

let vcons : string -> e_vbox -> e_vbox =
  fun c -> box_apply (fun v -> VCons(c,v))

let vreco : e_vbox A.t -> e_vbox =
  fun m -> box_apply (fun m -> VReco(m)) (A.lift_box m)

let vscis : e_vbox =
  box VScis

let vvdef : value -> e_vbox =
  fun v -> box (VVdef v)

(* Smart constructors for terms. *)
let tvalu : e_vbox -> e_tbox =
  box_apply (fun v -> TValu(v))

let tappl : e_tbox -> e_tbox -> e_tbox =
  box_apply2 (fun t u -> TAppl(t,u))

let tfixy : string -> (e_tvar -> e_vbox) -> e_tbox =
  fun x f -> box_apply (fun b -> TFixY(b)) (Bindlib.vbind mk_tvari x f)

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

let tprnt : string -> e_tbox =
  fun s -> box (TPrnt(s))

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

let rec step : proc -> proc option = function
  | (TValu(v)          , SEpsi      ) -> None
  | (TAppl(t,u)        , pi         ) -> Some (u, SFram(t,pi))
  | (TValu(v)          , SFram(t,pi)) -> Some (t, SPush(v,pi))
  | (TValu(VVdef(d))   , pi         ) -> step (TValu(d.value_eval), pi)
  | (TValu(VLAbs(b))   , SPush(v,pi)) -> Some (subst b v, pi)
  | (TFixY(b) as t     , pi         ) -> Some (TValu(subst b t), pi)
  | (TMAbs(b)          , pi         ) -> Some (subst b pi, pi)
  | (TName(pi,t)       , _          ) -> Some (t, pi)
  | (TProj(VVdef(d),l) , pi         ) -> step (TProj(d.value_eval,l), pi)
  | (TProj(VReco(m),l) , pi         ) ->
      begin
        try Some (TValu(A.find l m), pi)
        with Not_found -> runtime_error "Unknown record field"
      end
  | (TCase(VVdef(d),m)  , pi        ) -> step (TCase(d.value_eval,m), pi)
  | (TCase(VCons(c,v),m), pi        ) ->
      begin
        try Some (subst (A.find c m) v, pi)
        with Not_found -> runtime_error "Unknown constructor"
      end
  | (TPrnt(s)          , pi         ) ->
      begin
        output_string stdout s;
        Some (TValu(VReco(A.empty)), pi)
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
