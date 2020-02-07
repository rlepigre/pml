(** Expression comparing and unification. *)

open Sorts
open Ast
open Pos
open Output
open Iter

let log_uni = Log.register 'u' (Some "uni") "unification informations"
let log_uni = Log.(log_uni.p)

(* Unification variable equality test. *)
let uvar_eq : type a. a uvar -> a uvar -> bool =
  fun u v -> u.uvar_key == v.uvar_key

(** types used for the action in the iterator below *)
type uvar_fun = { f : 'a. 'a sort -> 'a uvar -> unit }
(** A small GADT for hash tbl below *)
type b = A : 'a ex -> b

exception Occurs

(** The iterator on unif variables appearing in an expression *)
let uvar_iter : type a. bool -> bool -> uvar_fun -> a ex loc -> unit =
  fun ignore_epsilon ignore_fixpoint f e ->
    let iterator : type a. recall -> a ex loc -> unit = fun {default} e ->
      let e = Norm.whnf e in
      match e.elt with
      | UVar(s,u)   -> f.f s u
      | _           -> default e
    in
    let iterator = { iterator; doclosed = false
                   ; dofixpnt = not ignore_fixpoint
                   ; doepsiln = not ignore_epsilon }
    in
    iter iterator e

(** use the iterator to collect all variables in an expression *)
let uvars : type a. ?ignore_epsilon:bool -> ?ignore_fixpoint:bool
                 -> a ex loc -> s_elt list =
  fun ?(ignore_epsilon=false) ?(ignore_fixpoint=false) e ->
  let uvars = ref [] in
  let f s u =
    let p (U(_,v)) = v.uvar_key == u.uvar_key in
    if not (List.exists p !uvars) then uvars := (U(s,u)) :: !uvars
  in
  uvar_iter ignore_epsilon ignore_fixpoint {f} e; !uvars

(** use the iterator to collect all variables in a binder *)
let bndr_uvars : type a b. ?ignore_epsilon:bool -> ?ignore_fixpoint:bool
                      -> a sort -> (a, b) bndr -> s_elt list =
  fun ?(ignore_epsilon=false) ?(ignore_fixpoint=false) s b ->
    uvars ~ignore_epsilon ~ignore_fixpoint (bndr_term b)

let occur_chrono = Chrono.create "occur"

(** occur check *)
let uvar_occurs : type a b. a uvar -> b ex loc -> bool = fun u e ->
  let f _ v =
    if v.uvar_key == u.uvar_key then
      begin
        log_uni "Occur check on %d" u.uvar_key;
        raise Occurs
      end
  in
  if !(u.uvar_pur) && not (Pure.pure e) then true else
  try Chrono.add_time occur_chrono (uvar_iter false false {f}) e; false
  with Occurs -> true

(** Occur check in constraints *)
let uvar_occurs_rel : type a. a uvar -> rel -> bool = fun u c ->
  match c with
  | Equiv(t,_,s) -> uvar_occurs u t || uvar_occurs u s
  | NoBox(v)     -> uvar_occurs u v

(** count "visible" uvars *)
let nb_vis_uvars a =
  List.length (uvars ~ignore_epsilon:true ~ignore_fixpoint:true a)
