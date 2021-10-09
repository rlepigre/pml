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
let vlabs : string -> (e_vvar -> e_tbox) -> e_vbox =
  fun x f ->
    box_apply
      (fun b -> VLAbs(b))
      (let v = new_var mk_vvari x in bind_var v (f v))

let vlazy : e_tbox -> e_vbox = box_apply (fun t -> VLazy(ref (Frz t)))

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

let tfrce : e_tbox -> e_tbox =
  box_apply (fun t -> TFrce t)

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

let tclck : e_vbox -> e_tbox =
  fun v -> box_apply (fun v -> TClck v) v

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


let read_clock =
  let clock = ref 0 in
  let rec fn = function
    | 0 -> VCons("Zero", VReco(A.empty))
    | n -> assert(n>0); VCons("S", fn (n-1))
  in
  (fun () ->
    let r = fn !clock in
    incr clock;
    r)

let rec eval : e_term -> e_stac -> e_valu = fun t s -> match (t, s) with
  | (TValu(v)          , SEpsi      ) -> v
  | (TValu(v)          , SFram(t,pi)) -> eval t (SPush(v,pi))
  | (TValu(VVdef(d))   , pi         ) -> eval (TValu(d.value_eval)) pi
  | (TValu(VLAbs(b))   , SPush(v,pi)) -> eval (subst b v) pi
  | (TClck(v)          , pi         ) ->
     eval t (SPush(VReco(A.add "1" (read_clock ())
                        (A.add "2" v A.empty)), pi))
  | (TValu(VLazy(e))   , SPush(_,pi)) ->
     let v =
       match !e with
       | Frz t -> let v = eval t SEpsi in e := Val v; v
       | Val v -> v
     in
     eval (TValu v) pi
  | (TAppl(t,u)        , pi         ) -> eval u (SFram(t,pi))
  | (TFrce(t)          , pi         ) -> eval t (SPush(VReco A.empty,pi))
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

let evalu_chrono = Chrono.create "evalu"

let eval : e_term -> e_valu = fun t ->
  Chrono.add_time evalu_chrono (eval t) SEpsi
