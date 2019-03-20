(** Evaluation in an abstract machine. *)

open Bindlib
open Ast

module A = Assoc

type e_vvar = e_valu Bindlib.var
type e_tvar = e_term Bindlib.var
type e_svar = e_stac Bindlib.var

type e_vbox = e_valu Bindlib.box
type e_tbox = e_term Bindlib.box
type e_sbox = e_stac Bindlib.box

let mk_vvari : e_valu Bindlib.var -> e_valu =
  fun x -> VVari(x)

let mk_tvari : e_term Bindlib.var -> e_term =
  fun x -> TVari(x)

let mk_svari : e_stac Bindlib.var -> e_stac =
  fun x -> SVari(x)

(* Smart constructors for values. *)
let vlabs : string -> (e_vvar -> e_tbox) -> bool -> e_vbox =
  fun x f tot ->
    box_apply
      (fun b ->
        let r = if not tot || binder_occur b then
                  None
                else Some (ref None)
        in VLAbs(b,r))
      (let v = new_var mk_vvari x in
       bind_var v (f v))

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
  fun x f -> box_apply (fun b -> TFixY(b))
                       (let v = new_var mk_tvari x in
                        bind_var v (f v))

let tmabs : string -> (e_svar -> e_tbox) -> e_tbox =
  fun x f -> box_apply (fun b -> TMAbs(b))
                       (let v = new_var mk_svari x in
                        bind_var v (f v))

let tname : e_sbox -> e_tbox -> e_tbox =
  box_apply2 (fun s t -> TName(s,t))

let tproj : e_vbox -> string -> e_tbox =
  fun v l -> box_apply (fun v -> TProj(v,l)) v

let tcase : e_vbox -> (string * (e_vvar -> e_tbox)) A.t -> e_tbox =
  fun v m ->
    let f (x,f) =
      let v = new_var mk_vvari x in
      bind_var v (f v)
    in
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

let use_lazy = ref true

let rec eval : e_term -> e_stac -> e_valu = fun t s -> match (t, s) with
  | (TValu(v)          , SEpsi      ) -> v
  | (TValu(v)          , SFram(t,pi)) -> eval t (SPush(v,pi))
  | (TValu(VVdef(d))   , pi         ) -> eval (TValu(d.value_eval)) pi
  | (TValu(VLAbs(b,r)) , SPush(v,pi)) ->
     begin
       match r with
       | Some r when !use_lazy ->
          let w =
            match !r with
            | Some w -> w
            | None   -> let w = eval (subst b v) SEpsi in
                        assert (!r = None); r := Some w; w
          in eval (TValu w) pi
       | _ -> eval (subst b v) pi
     end
  | (TAppl(t,u)        , pi         ) -> eval u (SFram(t,pi))
  | (TFixY(b) as t     , pi         ) -> eval (TValu(subst b t)) pi
  | (TMAbs(b)          , pi         ) -> eval (subst b pi) pi
  | (TName(pi,t)       , _          ) -> eval t pi
  | (TProj(VVdef(d),l) , pi         ) -> eval (TProj(d.value_eval,l)) pi
  | (TProj(VReco(m),l) , pi         ) ->
       begin
        try eval (TValu(A.find l m)) pi
        with Not_found -> runtime_error "Unknown record field"
      end
  | (TCase(VVdef(d),m)  , pi        ) -> eval (TCase(d.value_eval,m)) pi
  | (TCase(VCons(c,v),m), pi        ) ->
      begin
        try eval (subst (A.find c m) v) pi
        with Not_found -> runtime_error "Unknown constructor"
      end
  | (TPrnt(s)          , pi         ) ->
      begin
        Printf.printf "%s%!" s;
        eval (TValu(VReco(A.empty))) pi
      end
  (* Runtime errors. *)
  | (TProj(_)          , _          ) -> runtime_error "invalid projection"
  | (TCase(_,_)        , _          ) -> runtime_error "invalid case analysis"
  | (TVari(_)          , _          ) -> runtime_error "free term variable"
  | (TValu(_)          , _          ) -> runtime_error "free stack variable"

let eval : e_term -> e_valu = fun t -> eval t SEpsi
