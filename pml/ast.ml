(** Abstract syntax tree. This module defined the internal representation
    of PML's programs and higher-order type. *)

open Bindlib
open Sorts
open Pos

(** Module for Maps with [string] keys. *)
module StrMap = Map.Make(String)
module M =
  struct
    include StrMap

    let lift_box : 'a bindbox t -> 'a t bindbox =
      fun m -> let module B = Lift(StrMap) in B.f m

    let map_box : ('b -> 'a bindbox) -> 'b t -> 'a t bindbox =
      fun f m -> lift_box (map f m)
  end

(** Type of a (bindlib) binder with support for positions.
    @see <https://www.lama.univ-savoie.fr/~raffalli/bindlib.html> bindlib *)
type (-'a, +'b) lbinder = pos option * ('a, 'b loc) binder
(** The optional position refers to the bound variable. *)

(** Substitution function. *)
let lsubst : ('a, 'b) lbinder -> 'a -> 'b loc =
  fun (_,b) t -> subst b t

let lbinder_cmp : ('a, 'b) lbinder -> ('b loc -> 'c loc) -> ('a, 'c) lbinder =
  fun (p, b) f -> (p, binder_compose_right b f)

let lbinder_name : ('a, 'b) lbinder -> string =
  fun (_, b) -> binder_name b

let lbinder_from_fun : string -> ('a -> 'b) -> ('a,'b) lbinder =
  fun x f -> assert false

(** Unification variable type. *)
type 'a uvar =
  { uvar_key : int
  ; uvar_val : 'a option ref }

(** {6 Main abstract syntax tree type} *)

(** Type of (well-sorted) expressions. This is the core abstract syntax
    representation of our language. Everything is unified as a single GADT
    to allow for higher-order types. *)
type _ ex =
  (* Variables. *)

  | Vari : 'a ex variable                                     -> 'a ex
  (** Variables (of some sort). *)

  (* Higher order stuff. *)

  | HFun : ('a ex, 'b ex) lbinder                             -> ('a -> 'b) ex
  (** Higher-order function (e.g. parametric type). *)
  | HApp : 'a sort * ('a -> 'b) ex loc * 'a ex loc            -> 'b ex
  (** Corresponding higher-order application. *)

  (* Proposition constructors. *)

  | Func : p ex loc * p ex loc                                -> p ex
  (** Arrow type. *)
  | Prod : (pos option * p ex loc) M.t                        -> p ex
  (** Product (or record) type. *)
  | DSum : (pos option * p ex loc) M.t                        -> p ex
  (** Disjoint sum type. *)
  | Univ : 'a sort * ('a ex, p ex) lbinder                    -> p ex
  (** Universal quantification (e.g. polymorphism). *)
  | Exis : 'a sort * ('a ex, p ex) lbinder                    -> p ex
  (** Existential quantification (e.g. type abstraction). *)
  | FixM : o ex loc * (p ex, p ex) lbinder                    -> p ex
  (** Inductive type with an ordinal size. *)
  | FixN : o ex loc * (p ex, p ex) lbinder                    -> p ex
  (** Coinductive type with an ordinal size. *)
  | Memb : t ex loc * p ex loc                                -> p ex
  (** Membership type. *)
  | Rest : p ex loc * (t ex loc * bool * t ex loc)            -> p ex
  (** Restriction type. *)

  (* Value constructors. *)

  | LAbs : p ex loc option * (v ex, t ex) lbinder             -> v ex
  (** Lambda abstraction. *)
  | Cons : M.key loc * v ex loc                               -> v ex
  (** Constructor with exactly one argument. *)
  | Reco : (pos option * v ex loc) M.t                        -> v ex
  (** Record (i.e. tuple with named fields). *)
  | Scis :                                                       v ex
  (** PML scisors. *)

  (* Term constructors. *)

  | Valu : v ex loc                                           -> t ex
  (** Value as a term. *)
  | Appl : t ex loc * t ex loc                                -> t ex
  (** Application. *)
  | MAbs : p ex loc option * (s ex, t ex) lbinder             -> t ex
  (** Mu abstraction. *)
  | Name : s ex loc * t ex loc                                -> t ex
  (** Named term. *)
  | Proj : v ex loc * M.key loc                               -> t ex
  (** Record projection. *)
  | Case : v ex loc * (pos option * (v ex, t ex) lbinder) M.t -> t ex 
  (** Case analysis. *)
  | FixY : t ex loc * v ex loc                                -> t ex
  (** Fixpoint combinator. *)

  (* Stack constructors. *)

  | Epsi :                                                       s ex
  (** Empty stack. *)
  | Push : v ex loc * s ex loc                                -> s ex
  (** Value pushed on a stack. *)
  | Fram : t ex loc * s ex loc                                -> s ex
  (** Stack frame. *)

  (* Ordinal constructors. *)

  | Conv :                                                       o ex
  (** Maximal ordinal. *)
  | Succ : o ex loc                                           -> o ex
  (** Successor of an ordinal. *)

  (* Type annotations. *)

  | VTyp : v ex loc * p ex loc                                -> v ex
  (** Type coercion on a term. *)
  | TTyp : t ex loc * p ex loc                                -> t ex
  (** Type coercion on a term. *)
  | VLam : 'a sort * ('a ex, v ex) lbinder                    -> v ex
  (** Type abstraction on a value. *)
  | TLam : 'a sort * ('a ex, t ex) lbinder                    -> t ex
  (** Type abstraction on a term. *)

  (* Special constructors. *)

  | ITag : int                                                -> 'a ex
  (** Integer tag (usuful for comparision). *)
  | Dumm :                                                       'a ex
  (** Dummy constructor.*)
  | VWit : (v ex, t ex) lbinder * p ex loc * p ex loc         -> v ex
  (** Value witness (a.k.a. epsilon). *)
  | SWit : (s ex, t ex) lbinder * p ex loc                    -> s ex
  (** Stack witness (a.k.a. epsilon). *)
  | UWit : 'a sort * t ex loc * ('a ex, p ex) lbinder         -> 'a ex
  (** Universal quantifier witness (a.k.a. epsilon). *)
  | EWit : 'a sort * t ex loc * ('a ex, p ex) lbinder         -> 'a ex
  (** Existential quantifier witness (a.k.a. epsilon). *)
  | UVar : 'a sort * 'a ex loc uvar                           -> 'a ex
  (** Unification variable. *)
  (* TODO add MuRec and NuRec *)

type ordi = o ex loc (** Type of ordinals. *)
type prop = p ex loc (** Type of types.    *)
type valu = v ex loc (** Type of values.   *)
type term = t ex loc (** Type of terms.    *)
type stac = s ex loc (** Type of stacks.   *)

(** {6 Smart constructors} *)

type popt = pos option
type 'a var = 'a ex variable
type 'a box = 'a ex loc bindbox

type vvar = v var
type tvar = t var
type svar = s var
type pvar = p var
type ovar = o var

type vbox = v box
type tbox = t box
type sbox = s box
type pbox = p box
type obox = o box

let mk_free : 'a var -> 'a ex =
  fun x -> Vari(x)

(** {5 Higher order stuff} *)

let vari : type a. popt -> a var -> a ex loc bindbox =
  fun pos x -> box_apply (fun x -> {elt = x; pos}) (box_of_var x)

let hfun : type a b. popt -> strloc -> (a var -> b box) -> (a -> b) box =
  fun pos x f ->
    let b = vbind mk_free x.elt f in
    box_apply (fun b -> {elt = HFun((x.pos, b)); pos}) b

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
let sugar_proj : popt -> tbox -> strloc -> tbox =
  fun pos t l ->
    let f x = proj pos (v_vari None x) l in
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

let rest : popt -> pbox -> (tbox * bool * tbox) -> pbox =
  fun pos a (t,b,u) ->
    let e = box_apply2 (fun t u -> (t,b,u)) t u in
    box_apply2 (fun a e -> {elt = Rest(a,e); pos}) a e

(** {5 Ordinal constructors} *)

let o_vari : popt -> ovar -> obox = vari

let conv : popt -> obox =
  fun pos -> box {elt = Conv; pos}

let succ : popt -> obox -> obox =
  fun pos -> box_apply (fun o -> {elt = Succ(o); pos})

(** {5 other constructors} *)

let dumm : 'a ex loc =
  {elt = Dumm; pos = None}
