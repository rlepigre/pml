(** Abstract syntax tree. This module defined the internal representation of
    PML's programs and higher-order type. *)

open Bindlib
open Sorts
open Eval
open Pos

module M = Map.Make(String)
module A = Assoc

(** {6 Main abstract syntax tree type} *)

(** Type of (well-sorted) expressions, which is the core PML abstract syntax
    representation. Everything is unified as a single GADT as  the  language
    provides higher-order types. *)
type _ ex =
  (* Variables. *)

  | Vari : 'a sort * 'a var                        -> 'a ex
  (** Variables (of some sort). *)

  (* Higher order stuff. *)

  | HFun : 'a sort * 'b sort * ('a, 'b) bndr       -> ('a -> 'b) ex
  (** Higher-order function. *)
  | HApp : 'a sort * ('a -> 'b) ex loc * 'a ex loc -> 'b ex
  (** Corresponding higher-order application. *)
  | HDef : 'a sort * 'a expr                       -> 'a ex
  (** Definition of an expression. *)

  (* Proposition constructors. *)

  | Func : p ex loc * p ex loc                     -> p  ex
  (** Arrow type. *)
  | Prod : (pos option * p ex loc) A.t             -> p  ex
  (** Product (or record) type. *)
  | DSum : (pos option * p ex loc) A.t             -> p  ex
  (** Disjoint sum type. *)
  | Univ : 'a sort * ('a, p) bndr                  -> p  ex
  (** Universal quantification. *)
  | Exis : 'a sort * ('a, p) bndr                  -> p  ex
  (** Existential quantification. *)
  | FixM : o ex loc * (p, p) bndr                  -> p  ex
  (** Inductive type with an ordinal size. *)
  | FixN : o ex loc * (p, p) bndr                  -> p  ex
  (** Coinductive type with an ordinal size. *)
  | Memb : t ex loc * p ex loc                     -> p  ex
  (** Membership type. *)
  | Rest : p ex loc * cond                         -> p  ex
  (** Restriction type. *)
  | Impl : cond * p ex loc                         -> p  ex
  (** Conditional implication. *)

  (* Value constructors. *)

  | LAbs : p ex loc option * (v, t) bndr           -> v  ex
  (** Lambda abstraction. *)
  | Cons : A.key loc * v ex loc                    -> v  ex
  (** Constructor with exactly one argument. *)
  | Reco : (popt * v ex loc) A.t                   -> v  ex
  (** Record. *)
  | Scis :                                            v  ex
  (** PML scisors. *)
  | VDef : value                                   -> v  ex
  (** Definition of a value. *)

  (* Term constructors. *)

  | Valu : v ex loc                                -> t  ex
  (** Value as a term. *)
  | Appl : t ex loc * t ex loc                     -> t  ex
  (** Application. *)
  | MAbs : (s, t) bndr                             -> t  ex
  (** Mu abstraction. *)
  | Name : s ex loc * t ex loc                     -> t  ex
  (** Named term. *)
  | Proj : v ex loc * A.key loc                    -> t  ex
  (** Record projection. *)
  | Case : v ex loc * (popt * (v, t) bndr) A.t     -> t  ex
  (** Case analysis. *)
  | FixY : (v, t) bndr * v ex loc                  -> t  ex
  (** Fixpoint combinator Y(λx.t, v). *)
  | Prnt : string                                  -> t  ex
  (** Printing instruction. *)

  (* Stack constructors. *)

  | Epsi :                                            s  ex
  (** Empty stack. *)
  | Push : v ex loc * s ex loc                     -> s  ex
  (** Value pushed on a stack. *)
  | Fram : t ex loc * s ex loc                     -> s  ex
  (** Stack frame. *)

  (* Ordinal constructors. *)

  | Conv :                                            o  ex
  (** Convergent ordinal. *)
  | Succ : o ex loc                                -> o  ex
  (** Successor of an ordinal. *)
  | OWMu : o ex loc * t ex loc * (o, p) bndr       -> o  ex
  (** Ordinal mu witness. *)
  | OWNu : o ex loc * t ex loc * (o, p) bndr       -> o  ex
  (** Ordinal nu witness. *)
  | OSch : o ex loc option * int * schema          -> o  ex
  (** Ordinal schema witness. *)

  (* Type annotations. *)

  | VTyp : v ex loc * p ex loc                     -> v  ex
  (** Type coercion on a term. *)
  | TTyp : t ex loc * p ex loc                     -> t  ex
  (** Type coercion on a term. *)

  (* Special constructors. *)

  | ITag : 'a sort * int                           -> 'a ex
  (** Integer tag (usuful for comparision). *)
  | Dumm :                                            'a ex
  (** Dummy constructor.*)
  | VWit : (v, t) bndr * p ex loc * p ex loc       -> v  ex
  (** Value witness. *)
  | SWit : (s, t) bndr * p ex loc                  -> s  ex
  (** Stack witness. *)
  | UWit : 'a sort * t ex loc * ('a, p) bndr       -> 'a ex
  (** Universal quantifier witness. *)
  | EWit : 'a sort * t ex loc * ('a, p) bndr       -> 'a ex
  (** Existential quantifier witness. *)
  | UVar : 'a sort * 'a uvar                       -> 'a ex
  (** Unification variable. *)
  | Goal : 'a sort * string                        -> 'a ex

and cond =
  | Equiv of (t ex loc * bool * t ex loc)
  (** Equivalence between terms. *)
  | Posit of o ex loc
  (** Positivity of the given ordinal. *)
  | NoBox of v ex loc
  (** Value that are not Box, i.e. real value *)

and 'a expr =
  { expr_name : strloc
  ; expr_def  : 'a ex loc }

and value =
  { value_name : strloc
  ; value_orig : t ex loc
  ; value_type : p ex loc
  ; value_eval : e_valu }

and fix_schema =
  { fsch_index : Scp.index (** index of the schema in the call graph *)
  ; fsch_judge : (v,t) bndr * (o ex, p ex loc) mbinder (** judgement *) }
  (* NOTE: [sch_judge = (vb,mob)] represents "λx.Y(λr.t, x) : a" where
     [mob] corresponds to "λr.t" and "mob" corresponds to "a", which is
     the only part of the judgment which can contain parameters. *)

and sub_schema =
  { ssch_index : Scp.index (** index of the schema in the call graph *)
  ; ssch_relat : (int * int) list (** relation between ordinals:
                                      j > i && j > 0, i and j being
                                      indexes in the mbinder below *)
  ; ssch_judge : (o ex, p ex loc * p ex loc) mbinder (** judgement *) }

and schema =
  | FixSch of fix_schema
  | SubSch of sub_schema

and fix_specialised =
  { fspe_param : o ex loc array
  ; fspe_judge : (v,t) bndr * p ex loc }

and sub_specialised =
  { sspe_param : o ex loc array
  ; sspe_relat : (o ex loc * o ex loc) list
  ; sspe_judge : p ex loc * p ex loc }

(** Type of unification variables. *)
and 'a uvar =
  { uvar_key : int
  ; uvar_val : 'a ex loc option ref }

(** {6 Types and functions related to binders and variables.} *)

(** Type of a (bindlib) variable.
    @see <https://www.lama.univ-savoie.fr/~raffalli/bindlib.html> bindlib *)
and 'a var = 'a ex Bindlib.var

(** Type of a (bindlib) binder with support for positions.
    @see <https://www.lama.univ-savoie.fr/~raffalli/bindlib.html> bindlib *)
and ('a, 'b) bndr = popt * ('a ex, 'b ex loc) binder

(** Type of an expression in a (bindlib) bindbox.
    @see <https://www.lama.univ-savoie.fr/~raffalli/bindlib.html> bindlib *)
and 'a box = 'a ex loc bindbox

(** Binder substitution function. *)
let bndr_subst : ('a, 'b) bndr -> 'a ex -> 'b ex loc =
  fun (_,b) t -> subst b t

(** Obtain the name of a bound variable in the form of a located string. The
    position corresponds to the variable in binding position. *)
let bndr_name : ('a, 'b) bndr -> strloc =
  fun (p, b) -> Pos.make p (binder_name b)

(** [bndr_from_fun x f] builds a binder using [x] as a name  for  the  bound
    variable, and the function [f] as a definition. *)
let bndr_from_fun : string -> ('a ex -> 'b ex) -> ('a,'b) bndr =
  fun x f -> (None, binder_from_fun x (fun x -> none (f x)))

(** [bndr_closed f] tells whether the binder [b] is closed. *)
let bndr_closed : ('a, 'b) bndr -> bool =
  fun (_,b) -> binder_closed b

(** {6 Types for the syntactic element of base sorts} *)

type valu = v ex loc (** Type of values.   *)
type term = t ex loc (** Type of terms.    *)
type stac = s ex loc (** Type of stacks.   *)
type prop = p ex loc (** Type of types.    *)
type ordi = o ex loc (** Type of ordinals. *)

(** {5 Bindlib variable types for expressions of base sort} *)

type vvar = v var    (** Value   variable type. *)
type tvar = t var    (** Term    variable type. *)
type svar = s var    (** Stack   variable type. *)
type pvar = p var    (** Type    variable type. *)
type ovar = o var    (** Ordinal variable type. *)

type omvar = ovar array (** Ordinal multiple variable type. *)

(** {5 Bindlib bindboxes containing expressions of base sort} *)

type vbox = v box    (** Value   bindbox type. *)
type tbox = t box    (** Term    bindbox type. *)
type sbox = s box    (** Stack   bindbox type. *)
type pbox = p box    (** Type    bindbox type. *)
type obox = o box    (** Ordinal bindbox type. *)

type condbox = cond bindbox

(** {6 Smart constructors} *)

let mk_free : 'a sort -> 'a var -> 'a ex =
  fun s x -> Vari(s, x)

(** {5 Higher order stuff} *)

let vari : type a. popt -> a var -> a ex loc bindbox =
  fun p x -> box_apply (fun x -> Pos.make p x) (box_of_var x)

let hfun : type a b. popt -> a sort -> b sort -> strloc -> (a var -> b box)
             -> (a -> b) box =
  fun p sa sb x f ->
    let b = vbind (mk_free sa) x.elt f in
    box_apply (fun b -> Pos.make p (HFun(sa, sb, (x.pos, b)))) b

let happ : type a b. popt -> a sort -> (a -> b) box -> a box -> b box =
  fun p s -> box_apply2 (fun f a -> Pos.make p (HApp(s,f,a)))

(** {5 Value constructors} *)

let v_vari : popt -> vvar -> vbox = vari

let labs : popt -> pbox option -> strloc -> (vvar -> tbox) -> vbox =
  fun p ao x f ->
    let b = vbind (mk_free V) x.elt f in
    box_apply2 (fun ao b -> Pos.make p (LAbs(ao, (x.pos, b)))) (box_opt ao) b

let cons : popt -> strloc -> vbox -> vbox =
  fun p c -> box_apply (fun v -> Pos.make p (Cons(c,v)))

let reco : popt -> (popt * vbox) A.t -> vbox =
  fun p m ->
    let f (lpos, v) = box_apply (fun v -> (lpos, v)) v in
    box_apply (fun m -> Pos.make p (Reco(m))) (A.map_box f m)

let unit_reco = reco None A.empty
let scis : popt -> vbox =
  fun pos -> box (Pos.make pos Scis)

let vtyp : popt -> vbox -> pbox -> vbox =
  fun p -> box_apply2 (fun v a -> Pos.make p (VTyp(v,a)))

(** {5 Term constructors} *)

let t_vari : popt -> tvar -> tbox = vari

let valu : popt -> vbox -> tbox =
  fun p -> box_apply (fun v -> Pos.make p (Valu v))

let appl : popt -> tbox -> tbox -> tbox =
  fun p -> box_apply2 (fun t u -> Pos.make p (Appl(t,u)))

let sequ : popt -> tbox -> tbox -> tbox =
  fun p t u ->
    appl p (valu None (labs None None (Pos.none "_") (fun _ -> u))) t

let mabs : popt -> strloc -> (svar -> tbox) -> tbox =
  fun p x f ->
    let b = vbind (mk_free S) x.elt f in
    box_apply (fun b -> Pos.make p (MAbs(x.pos, b))) b

let name : popt -> sbox -> tbox -> tbox =
  fun p -> box_apply2 (fun s t -> Pos.make p (Name(s,t)))

let proj : popt -> vbox -> strloc -> tbox =
  fun p v l -> box_apply (fun v -> Pos.make p (Proj(v,l))) v

let case : popt -> vbox -> (popt * strloc * (vvar -> tbox)) A.t -> tbox =
  fun p v m ->
    let f (cpos, x, f) =
      let b = vbind (mk_free V) x.elt f in
      box_apply (fun b -> (cpos, (x.pos, b))) b
    in
    box_apply2 (fun v m -> Pos.make p (Case(v,m))) v (A.map_box f m)

let fixy : popt -> strloc -> (vvar -> tbox) -> vbox -> tbox =
  fun p x f v ->
    let b = vbind (mk_free V) x.elt f in
    box_apply2 (fun b v -> Pos.make p (FixY((x.pos, b),v))) b v

let prnt : popt -> string -> tbox =
  fun p s -> box (Pos.make p (Prnt(s)))

let ttyp : popt -> tbox -> pbox -> tbox =
  fun p -> box_apply2 (fun t a -> Pos.make p (TTyp(t,a)))

(** {5 Stack constructors} *)

let s_vari : popt -> svar -> sbox = vari

let epsi : popt -> sbox =
  fun p -> box (Pos.make p Epsi)

let push : popt -> vbox -> sbox -> sbox =
  fun p -> box_apply2 (fun v s -> Pos.make p (Push(v,s)))

let fram : popt -> tbox -> sbox -> sbox =
  fun p -> box_apply2 (fun t s -> Pos.make p (Fram(t,s)))

(** {5 Proposition constructors} *)

let p_vari : popt -> pvar -> pbox = vari

let func : popt -> pbox -> pbox -> pbox =
  fun p -> box_apply2 (fun a b -> Pos.make p (Func(a,b)))

let prod : popt -> (popt * pbox) A.t -> pbox =
  fun p m ->
    let f (lpos, a) = box_apply (fun a -> (lpos, a)) a in
    box_apply (fun m -> Pos.make p (Prod(m))) (A.map_box f m)

let unit_prod = prod None A.empty

let dsum : popt -> (popt * pbox) A.t -> pbox =
  fun p m ->
    let f (lpos, a) = box_apply (fun a -> (lpos, a)) a in
    box_apply (fun m -> Pos.make p (DSum(m))) (A.map_box f m)

let univ : type a. popt -> strloc -> a sort -> (a var -> pbox) -> pbox =
  fun p x s f ->
    let b = vbind (mk_free s) x.elt f in
    box_apply (fun b -> Pos.make p (Univ(s, (x.pos, b)))) b

let exis : type a. popt -> strloc -> a sort -> (a var -> pbox) -> pbox =
  fun p x s f ->
    let b = vbind (mk_free s) x.elt f in
    box_apply (fun b -> Pos.make p (Exis(s, (x.pos, b)))) b

let fixm : popt -> obox -> strloc -> (pvar -> pbox) -> pbox =
  fun p o x f ->
    let b = vbind (mk_free P) x.elt f in
    box_apply2 (fun o b -> Pos.make p (FixM(o, (x.pos, b)))) o b

let fixn : popt -> obox -> strloc -> (pvar -> pbox) -> pbox =
  fun p o x f ->
    let b = vbind (mk_free P) x.elt f in
    box_apply2 (fun o b -> Pos.make p (FixN(o, (x.pos, b)))) o b

let memb : popt -> tbox -> pbox -> pbox =
  fun p -> box_apply2 (fun t a -> Pos.make p (Memb(t,a)))

let rest : popt -> pbox -> condbox -> pbox =
  fun p -> box_apply2 (fun a c -> Pos.make p (Rest(a,c)))

let impl : popt -> condbox -> pbox -> pbox =
  fun p -> box_apply2 (fun c a -> Pos.make p (Impl(c,a)))

(** {5 Condition constructors} *)

let equiv : tbox -> bool -> tbox -> condbox =
  fun t b u ->
    box_apply2 (fun t u -> Equiv(t,b,u)) t u

let posit : obox -> condbox =
  box_apply (fun o -> Posit(o))

let nobox : vbox -> condbox =
  box_apply (fun v -> NoBox(v))

(** {5 Ordinal constructors} *)

let o_vari : popt -> ovar -> obox = vari

let conv : popt -> obox =
  fun p -> box (Pos.make p Conv)

let succ : popt -> obox -> obox =
  fun p -> box_apply (fun o -> Pos.make p (Succ(o)))

let goal : type a. popt -> a sort -> string -> a ex loc bindbox =
  fun p s str -> box (Pos.make p (Goal(s,str)))

(** {5 syntactic sugars} *)

(** Syntactic sugar for the projection of a term. *)
let t_proj : popt -> tbox -> strloc -> tbox =
  fun p t l ->
    let f x = proj p (v_vari None x) l in
    let u = valu p (labs p None (Pos.none "x") f) in
    appl p u t

(** Syntactic sugar for the case analysis on a term. *)
let t_case : popt -> tbox -> (popt * strloc * (vvar -> tbox)) A.t -> tbox =
  fun p t m ->
    let f x = case p (vari None x) m in
    let u = valu p (labs p None (Pos.none "x") f) in
    appl p u t

(** Syntactic sugar for a constructor applied to a term. *)
let t_cons : popt -> strloc -> tbox -> tbox =
  fun p c t ->
    let f x = valu p (cons p c (vari None x)) in
    let u = valu p (labs p None (Pos.none "x") f) in
    appl p u t

(** Syntactic sugar for records containing terms. *)
let t_reco : popt -> (string * (popt*tbox)) list -> (popt*vbox) A.t -> tbox =
  fun p tfs m ->
    let fn env =
      let add m (l,_) = A.add l (None, List.assoc l env) m in
      valu p (reco p (List.fold_left add m tfs))
    in
    let rec build env xs =
      match xs with
      | []    -> fn env
      | x::xs -> let fn y = build ((x, vari None y) :: env) xs in
                 valu None (labs None None (Pos.none x) fn)
    in
    let f = build [] (List.map fst tfs) in
    let ts = List.map (fun (_,(_,t)) -> t) tfs in
    List.fold_left (appl None) f ts

(** Syntactic sugar for strict product type. *)
let strict_prod : popt -> (popt * pbox) A.t -> pbox =
  fun p m ->
    let fn env = reco None (A.mapi (fun l _ -> (None, List.assoc l env)) m) in
    let rec build env ls =
      match ls with
      | []    -> memb None (valu None (fn env)) (prod p m)
      | l::ls -> let fn (x:vvar) = build ((l, vari None x) :: env) ls in
                 exis None (Pos.none l) V fn
    in
    build [] (List.map fst (A.bindings m))

(** {5 useful functions} *)

let rec is_scis : type a. a ex loc -> bool =
  fun e ->
    match e.elt with
    | Scis    -> true
    | Valu(v) -> is_scis v
    | _       -> false

let build_v_fixy : (v,t) bndr -> valu = fun b ->
  let f x = box_apply (fun x -> Pos.none (FixY(b,x))) (v_vari None x) in
  unbox (labs None None (Pos.none "x") f)

let build_t_fixy : (v,t) bndr -> term = fun b ->
  Pos.none (Valu(build_v_fixy b))


let rec sort : type a b. a ex loc ->  a sort * a ex loc= fun e ->
  match e.elt with
  | HDef(s,_)   -> (s, e)
  | HApp(d,u,v) -> let (F(_,s),_) = sort u in (s,e)
  | HFun(d,c,r) -> (F(d, c), e)
  | UWit(s,_,_) -> (s,e)
  | EWit(s,_,_) -> (s,e)
  | UVar(s,_)   -> (s,e)
  | ITag(s,_)   -> (s,e)
  | Goal(s,_)   -> (s,e)

  | Func _      -> (P,e)
  | Prod _      -> (P,e)
  | DSum _      -> (P,e)
  | Univ _      -> (P,e)
  | Exis _      -> (P,e)
  | FixM _      -> (P,e)
  | FixN _      -> (P,e)
  | Memb _      -> (P,e)
  | Rest _      -> (P,e)
  | Impl _      -> (P,e)

  | VWit _      -> (V,e)
  | LAbs _      -> (V,e)
  | Cons _      -> (V,e)
  | Reco _      -> (V,e)
  | Scis        -> (V,e)
  | VDef _      -> (V,e)
  | VTyp _      -> (V,e)

  | Valu _      -> (T,e)
  | Appl _      -> (T,e)
  | MAbs _      -> (T,e)
  | Name _      -> (T,e)
  | Proj _      -> (T,e)
  | Case _      -> (T,e)
  | FixY _      -> (T,e)
  | Prnt _      -> (T,e)
  | TTyp _      -> (T,e)

  | Epsi        -> (S,e)
  | Push _      -> (S,e)
  | Fram _      -> (S,e)
  | SWit _      -> (S,e)

  | Conv        -> (O,e)
  | Succ _      -> (O,e)
  | OWMu _      -> (O,e)
  | OWNu _      -> (O,e)
  | OSch _      -> (O,e)

  | Vari(s,_)   -> (s,e)
  | Dumm        -> Output.bug_msg "Dumm in Ast.sort"; assert false

let isVal : type a.a ex loc -> v ex loc option = fun e ->
  match sort e with
  | (V,e)               -> Some e
  | (T,{ elt = Valu e}) -> Some e
  | _                   -> None

let isTerm : type a.a ex loc -> t ex loc option = fun e ->
  match sort e with
  | (V,e) -> Some (Pos.none (Valu e))
  | (T,e) -> Some e
  | _     -> None

let vdot : valu -> string -> term = fun v c ->
  let f x = valu None (vari None x) in
  let id = (None, Pos.none "x", f) in
  unbox (case None (box v) (A.singleton c id))
