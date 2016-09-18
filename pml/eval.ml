open Bindlib
open Pos
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

type e_vvar = e_valu variable
type e_tvar = e_term variable
type e_svar = e_stac variable

type e_vbox = e_valu bindbox
type e_tbox = e_term bindbox
type e_sbox = e_stac bindbox

let mk_vvari : e_valu variable -> e_valu =
  fun x -> VVari(x)

let mk_tvari : e_term variable -> e_term =
  fun x -> TVari(x)

let mk_svari : e_stac variable -> e_stac =
  fun x -> SVari(x)

(* Smart constructors for values. *)
let vlabs : string -> (e_vvar -> e_tbox) -> e_vbox =
  fun x f -> box_apply (fun b -> VLAbs(b)) (vbind mk_vvari x f)

let vcons : string -> e_vbox -> e_vbox =
  fun c -> box_apply (fun v -> VCons(c,v))

let vreco : e_vbox M.t -> e_vbox =
  fun m -> box_apply (fun m -> VReco(m)) (M.lift_box m)

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

let tcase : e_vbox -> (string * (e_vvar -> e_tbox)) M.t -> e_tbox =
  fun v m ->
    let f (x,f) = vbind mk_vvari x f in
    box_apply2 (fun v m -> TCase(v,m)) v (M.map_box f m)

let tfixy : e_tbox -> e_vbox -> e_tbox =
  box_apply2 (fun t v -> TFixY(t,v))

(* Smart constructors for stacks. *)
let sepsi : e_sbox =
  box SEpsi

let spush : e_vbox -> e_sbox -> e_sbox =
  box_apply2 (fun v s -> SPush(v,s))

let sfram : e_tbox -> e_sbox -> e_sbox =
  box_apply2 (fun t s -> SFram(t,s))

(* Erasure. *)

exception Erasure_error of string
let erasure_error : type a. string -> a =
  fun msg -> raise (Erasure_error msg)

let rec valu_erasure : valu -> e_vbox = fun v ->
  let v = Norm.whnf v in
  match v.elt with
  | Vari(x)   -> box_of_var (copy_var x (name_of x) mk_vvari)
  | HApp(_,_) -> erasure_error "not a normalisation value (value)"
  | LAbs(_,b) -> let f x =
                   let x = copy_var x (name_of x) mk_free in
                   term_erasure (lsubst b (free_of x))
                 in vlabs (binder_name (snd b)) f
  | Cons(c,v) -> vcons c.elt (valu_erasure v)
  | Reco(m)   -> vreco (M.map (fun (_,v) -> valu_erasure v) m)
  | Scis      -> vscis
  | VTyp(v,_) -> valu_erasure v
  | VLam(f)   -> valu_erasure (lsubst f Dumm)
  | ITag(_)   -> erasure_error "a tag cannot be erased (value)"
  | Dumm      -> erasure_error "a dummy value cannot be erased (value)"
  | VWit(_)   -> erasure_error "a witness cannot be erased (value)"
  | UWit(_)   -> erasure_error "a witness cannot be erased (value)"
  | EWit(_)   -> erasure_error "a witness cannot be erased (value)"
  | UVar(_)   -> erasure_error "unif. variables cannot be erased (value)"

and     term_erasure : term -> e_tbox = fun t ->
  let t = Norm.whnf t in
  match t.elt with
  | Vari(x)   -> box_of_var (copy_var x (name_of x) mk_tvari)
  | HApp(_,_) -> erasure_error "not a normalisation value (term)"
  | Valu(v)   -> tvalu (valu_erasure v)
  | Appl(t,u) -> tappl (term_erasure t) (term_erasure u)
  | MAbs(_,b) -> let f x =
                   let x = copy_var x (name_of x) mk_free in
                   term_erasure (lsubst b (free_of x))
                 in tmabs (binder_name (snd b)) f
  | Name(s,t) -> tname (stac_erasure s) (term_erasure t)
  | Proj(v,l) -> tproj (valu_erasure v) l.elt
  | Case(v,m) -> let f (_,b) =
                   let f x =
                     let x = copy_var x (name_of x) mk_free in
                     term_erasure (lsubst b (free_of x))
                   in (binder_name (snd b), f)
                 in tcase (valu_erasure v) (M.map f m)
  | FixY(t,v) -> tfixy (term_erasure t) (valu_erasure v)
  | TTyp(t,_) -> term_erasure t
  | TLam(f)   -> term_erasure (lsubst f Dumm)
  | ITag(_)   -> erasure_error "a tag cannot be erased (term)"
  | Dumm      -> erasure_error "a dummy value cannot be erased (term)"
  | UWit(_)   -> erasure_error "a witness cannot be erased (term)"
  | EWit(_)   -> erasure_error "a witness cannot be erased (term)"
  | UVar(_)   -> erasure_error "unif. variables cannot be erased (term)"

and     stac_erasure : stac -> e_sbox = fun s ->
  let s = Norm.whnf s in
  match s.elt with
  | Vari(x)   -> box_of_var (copy_var x (name_of x) mk_svari)
  | HApp(_,_) -> erasure_error "not a normalisation value (stack)"
  | Epsi      -> sepsi
  | Push(v,s) -> spush (valu_erasure v) (stac_erasure s)
  | Fram(t,s) -> sfram (term_erasure t) (stac_erasure s)
  | ITag(_)   -> erasure_error "a tag cannot be erased (stack)"
  | Dumm      -> erasure_error "a dummy value cannot be erased (stack)"
  | SWit(_,_) -> erasure_error "a witness cannot be erased (stack)"
  | UWit(_)   -> erasure_error "a witness cannot be erased (stack)"
  | EWit(_)   -> erasure_error "a witness cannot be erased (stack)"
  | UVar(_)   -> erasure_error "unif. variables cannot be erased (stack)"

let valu_erasure : valu -> e_valu =
  fun v -> unbox (valu_erasure v)

let term_erasure : term -> e_term =
  fun t -> unbox (term_erasure t)

let stac_erasure : stac -> e_stac =
  fun s -> unbox (stac_erasure s)

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
        try Some (TValu(M.find l m), pi)
        with Not_found -> runtime_error "Unknown record field"
      end
  | (TCase(VCons(c,v),m), pi        ) ->
      begin
        try Some (subst (M.find c m) v, pi)
        with Not_found -> runtime_error "Unknown constructor"
      end
  | (TFixY(t,v)        , pi         ) ->
      begin
        let f = fun x -> TFixY(t,x) in
        let b = binder_from_fun "x" f in
        Some (t, SPush(VLAbs(b),SPush(v,pi)))
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
