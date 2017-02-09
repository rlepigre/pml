(** Abstract syntax tree. This module defined the internal representation of
    PML's programs and higher-order type. *)

open Bindlib
open Sorts
open Eval
open Pos

module M = Strmap

(** {6 Main abstract syntax tree type} *)

(** Type of (well-sorted) expressions, which is the core PML abstract syntax
    representation. Everything is unified as a single GADT as  the  language
    provides higher-order types. *)
type _ ex =
  (* Variables. *)

  | Vari : 'a var                                  -> 'a ex
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
  | Prod : (pos option * p ex loc) M.t             -> p  ex
  (** Product (or record) type. *)
  | DSum : (pos option * p ex loc) M.t             -> p  ex
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
  | Cons : M.key loc * v ex loc                    -> v  ex
  (** Constructor with exactly one argument. *)
  | Reco : (popt * v ex loc) M.t                   -> v  ex
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
  | MAbs : p ex loc option * (s, t) bndr           -> t  ex
  (** Mu abstraction. *)
  | Name : s ex loc * t ex loc                     -> t  ex
  (** Named term. *)
  | Proj : v ex loc * M.key loc                    -> t  ex
  (** Record projection. *)
  | Case : v ex loc * (popt * (v, t) bndr) M.t     -> t  ex 
  (** Case analysis. *)
  | FixY : t ex loc * v ex loc                     -> t  ex
  (** Fixpoint combinator. *)

  (* Stack constructors. *)

  | Epsi :                                            s  ex
  (** Empty stack. *)
  | Push : v ex loc * s ex loc                     -> s  ex
  (** Value pushed on a stack. *)
  | Fram : t ex loc * s ex loc                     -> s  ex
  (** Stack frame. *)

  (* Ordinal constructors. *)

  | Conv :                                            o  ex
  (** Maximal ordinal. *)
  | Succ : o ex loc                                -> o  ex
  (** Successor of an ordinal. *)

  (* Type annotations. *)

  | VTyp : v ex loc * p ex loc                     -> v  ex
  (** Type coercion on a term. *)
  | TTyp : t ex loc * p ex loc                     -> t  ex
  (** Type coercion on a term. *)
  | VLam : 'a sort * ('a, v) bndr                  -> v  ex
  (** Type abstraction on a value. *)
  | TLam : 'a sort * ('a, t) bndr                  -> t  ex
  (** Type abstraction on a term. *)

  (* Special constructors. *)

  | ITag : int                                     -> 'a ex
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

and cond =
  | Equiv of (t ex loc * bool * t ex loc)
  (** Equivalence between terms. *)
  | Posit of o ex loc
  (** Positivity of the given ordinal. *)

and 'a expr =
  { expr_name : strloc
  ; expr_def  : 'a ex loc }

and value =
  { value_name : strloc
  ; value_orig : t ex loc
  ; value_type : p ex loc
  ; value_eval : e_valu }

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
  fun (p, b) -> build_pos p (binder_name b)

(** [bndr_from_fun x f] builds a binder using [x] as a name  for  the  bound
    variable, and the function [f] as a definition. *)
let bndr_from_fun : string -> ('a ex -> 'b ex) -> ('a,'b) bndr =
  fun x f -> (None, binder_from_fun x (fun x -> none (f x)))

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

(** {5 Bindlib bindboxes containing expressions of base sort} *)

type vbox = v box    (** Value   bindbox type. *)
type tbox = t box    (** Term    bindbox type. *)
type sbox = s box    (** Stack   bindbox type. *)
type pbox = p box    (** Type    bindbox type. *)
type obox = o box    (** Ordinal bindbox type. *)

type condbox = cond bindbox

(** {6 Smart constructors} *)

let mk_free : 'a var -> 'a ex =
  fun x -> Vari(x)

(** {5 Higher order stuff} *)

let vari : type a. popt -> a var -> a ex loc bindbox =
  fun pos x -> box_apply (fun x -> {elt = x; pos}) (box_of_var x)

let hfun : type a b. popt -> a sort -> b sort -> strloc -> (a var -> b box)
             -> (a -> b) box =
  fun pos sa sb x f ->
    let b = vbind mk_free x.elt f in
    box_apply (fun b -> {elt = HFun(sa, sb, (x.pos, b)); pos}) b

let happ : type a b. popt -> a sort -> (a -> b) box -> a box -> b box =
  fun pos s -> box_apply2 (fun f a -> {elt = HApp(s,f,a); pos})

(** {5 Value constructors} *)

let v_vari : popt -> vvar -> vbox = vari

let labs : popt -> pbox option -> strloc -> (vvar -> tbox) -> vbox =
  fun pos ao x f ->
    let b = vbind mk_free x.elt f in
    box_apply2 (fun ao b -> {elt = LAbs(ao, (x.pos, b)); pos}) (box_opt ao) b

let cons : popt -> strloc -> vbox -> vbox =
  fun pos c -> box_apply (fun v -> {elt = Cons(c,v); pos})

let reco : popt -> (popt * vbox) M.t -> vbox =
  fun pos m ->
    let f (lpos, v) = box_apply (fun v -> (lpos, v)) v in
    box_apply (fun m -> {elt = Reco(m); pos}) (M.map_box f m)

let scis : popt -> vbox =
  fun pos -> box {elt = Scis; pos}

let vtyp : popt -> vbox -> pbox -> vbox =
  fun pos -> box_apply2 (fun v p -> {elt = VTyp(v,p); pos})

let vlam : type a. popt -> strloc -> a sort -> (a var -> vbox) -> vbox =
  fun pos x s f ->
    let b = vbind mk_free x.elt f in
    box_apply (fun b -> {elt = VLam(s, (x.pos, b)); pos}) b
 
(** {5 Term constructors} *)

let t_vari : popt -> tvar -> tbox = vari

let valu : popt -> vbox -> tbox =
  fun pos -> box_apply (fun v -> {elt = Valu(v); pos})

let appl : popt -> tbox -> tbox -> tbox =
  fun pos -> box_apply2 (fun t u -> {elt = Appl(t,u); pos})

let mabs : popt -> pbox option -> strloc -> (svar -> tbox) -> tbox =
  fun pos ao x f ->
    let b = vbind mk_free x.elt f in
    box_apply2 (fun ao b -> {elt = MAbs(ao, (x.pos, b)); pos}) (box_opt ao) b

let name : popt -> sbox -> tbox -> tbox =
  fun pos -> box_apply2 (fun s t -> {elt = Name(s,t); pos})

let proj : popt -> vbox -> strloc -> tbox =
  fun pos v l -> box_apply (fun v -> {elt = Proj(v,l); pos}) v

let case : popt -> vbox -> (popt * strloc * (vvar -> tbox)) M.t -> tbox =
  fun pos v m ->
    let f (cpos, x, f) =
      let b = vbind mk_free x.elt f in
      box_apply (fun b -> (cpos, (x.pos, b))) b
    in
    box_apply2 (fun v m -> {elt = Case(v,m); pos}) v (M.map_box f m)

let fixy : popt -> tbox -> vbox -> tbox =
  fun pos -> box_apply2 (fun t v -> {elt = FixY(t,v); pos})

let ttyp : popt -> tbox -> pbox -> tbox =
  fun pos -> box_apply2 (fun t p -> {elt = TTyp(t,p); pos})

let tlam : type a. popt -> strloc -> a sort -> (a var -> tbox) -> tbox =
  fun pos x s f ->
    let b = vbind mk_free x.elt f in
    box_apply (fun b -> {elt = TLam(s, (x.pos, b)); pos}) b

(** Syntactic sugar for the projection of a term. *)
let t_proj : popt -> tbox -> strloc -> tbox =
  fun pos t l ->
    let f x = proj pos (v_vari None x) l in
    let u = valu pos (labs pos None (Pos.none "x") f) in
    appl pos u t

(** Syntactic sugar for the case analysis on a term. *)
let t_case : popt -> tbox -> (popt * strloc * (vvar -> tbox)) M.t -> tbox =
  fun pos t m ->
    let f x = case pos (vari None x) m in
    let u = valu pos (labs pos None (Pos.none "x") f) in
    appl pos u t

(** {5 Stack constructors} *)

let s_vari : popt -> svar -> sbox = vari

let epsi : popt -> sbox =
  fun pos -> box {elt = Epsi; pos}

let push : popt -> vbox -> sbox -> sbox =
  fun pos -> box_apply2 (fun v s -> {elt = Push(v,s); pos})

let fram : popt -> tbox -> sbox -> sbox =
  fun pos -> box_apply2 (fun t s -> {elt = Fram(t,s); pos})

(** {5 Proposition constructors} *)
 
let p_vari : popt -> pvar -> pbox = vari

let func : popt -> pbox -> pbox -> pbox =
  fun pos -> box_apply2 (fun a b -> {elt = Func(a,b); pos})

let prod : popt -> (popt * pbox) M.t -> pbox =
  fun pos m ->
    let f (lpos, a) = box_apply (fun a -> (lpos, a)) a in
    box_apply (fun m -> {elt = Prod(m); pos}) (M.map_box f m)

let dsum : popt -> (popt * pbox) M.t -> pbox =
  fun pos m ->
    let f (lpos, a) = box_apply (fun a -> (lpos, a)) a in
    box_apply (fun m -> {elt = DSum(m); pos}) (M.map_box f m)

let univ : type a. popt -> strloc -> a sort -> (a var -> pbox) -> pbox =
  fun pos x s f ->
    let b = vbind mk_free x.elt f in
    box_apply (fun b -> {elt = Univ(s, (x.pos, b)); pos}) b

let exis : type a. popt -> strloc -> a sort -> (a var -> pbox) -> pbox =
  fun pos x s f ->
    let b = vbind mk_free x.elt f in
    box_apply (fun b -> {elt = Exis(s, (x.pos, b)); pos}) b

let fixm : popt -> obox -> strloc -> (pvar -> pbox) -> pbox =
  fun pos o x f ->
    let b = vbind mk_free x.elt f in
    box_apply2 (fun o b -> {elt = FixM(o, (x.pos, b)); pos}) o b

let fixn : popt -> obox -> strloc -> (pvar -> pbox) -> pbox =
  fun pos o x f ->
    let b = vbind mk_free x.elt f in
    box_apply2 (fun o b -> {elt = FixN(o, (x.pos, b)); pos}) o b

let memb : popt -> tbox -> pbox -> pbox =
  fun pos -> box_apply2 (fun t a -> {elt = Memb(t,a); pos})

let rest : popt -> pbox -> condbox -> pbox =
  fun pos a c ->
    box_apply2 (fun a c -> {elt = Rest(a,c); pos}) a c

let impl : popt -> condbox -> pbox -> pbox =
  fun pos c a ->
    box_apply2 (fun c a -> {elt = Impl(c,a); pos}) c a

(** {5 Condition constructors} *)

let equiv : tbox -> bool -> tbox -> condbox =
  fun t b u ->
    box_apply2 (fun t u -> Equiv(t,b,u)) t u

let posit : obox -> condbox =
  box_apply (fun o -> Posit(o))

(** {5 Ordinal constructors} *)

let o_vari : popt -> ovar -> obox = vari

let conv : popt -> obox =
  fun pos -> box {elt = Conv; pos}

let succ : popt -> obox -> obox =
  fun pos -> box_apply (fun o -> {elt = Succ(o); pos})

(** {5 other constructors} *)

let dumm : 'a ex loc =
  {elt = Dumm; pos = None}

let uwit : type a. popt -> tbox -> strloc -> a sort -> (a var -> pbox)
             -> a box =
  fun pos t x s f ->
    let b = vbind mk_free x.elt f in
    box_apply2 (fun t b -> {elt = UWit(s, t, (x.pos, b)); pos}) t b

let ewit : type a. popt -> tbox -> strloc -> a sort -> (a var -> pbox)
             -> a box =
  fun pos t x s f ->
    let b = vbind mk_free x.elt f in
    box_apply2 (fun t b -> {elt = EWit(s, t, (x.pos, b)); pos}) t b

let vwit : popt -> strloc -> (vvar -> tbox) -> pbox -> pbox -> vbox =
  fun pos x f a c ->
    let b = vbind mk_free x.elt f in
    box_apply3 (fun b a c -> {elt = VWit((x.pos, b),a,c); pos}) b a c

let swit : popt -> strloc -> (svar -> tbox) -> pbox -> sbox =
  fun pos x f a ->
    let b = vbind mk_free x.elt f in
    box_apply2 (fun b a -> {elt = SWit((x.pos, b),a); pos}) b a

(** {5 useful functions} *)

let rec is_scis : type a. a ex loc -> bool =
  fun e ->
    match e.elt with
    | Scis    -> true
    | Valu(v) -> is_scis v
    | _       -> false
