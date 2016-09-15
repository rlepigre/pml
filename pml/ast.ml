(** Abstract syntax tree. This module defined the internal representation
    of PML's programs and higher-order type. *)

open Bindlib
open Position

(** Module for Maps with [string] keys. *)
module M = Map.Make(String)

(** Type of a (bindlib) binder with support for positions.
    @see <https://www.lama.univ-savoie.fr/~raffalli/bindlib.html> bindlib *)
type (-'a, +'b) lbinder = pos * ('a, 'b loc) binder

(** Substitution function. *)
let lsubst : ('a, 'b) lbinder -> 'a -> 'b loc =
  fun (_,b) t -> subst b t

let lbinder_cmp : ('a, 'b) lbinder -> ('b loc -> 'c loc) -> ('a, 'c) lbinder =
  fun (p, b) f -> (p, binder_compose_right b f)

type o (** Phantom type for the sort of ordinals. *)
type p (** Phantom type for the sort of types.    *)
type v (** Phantom type for the sort of values.   *)
type t (** Phantom type for the sort of terms.    *)
type s (** Phantom type for the sort of stacks.   *)

(** Representation of our sorts. *)
type _ sort =
  | O : o sort
  | P : p sort
  | V : v sort
  | T : t sort
  | S : s sort
  | F : 'a sort * 'b sort -> ('a -> 'b) sort

(** Type of (well-sorted) expressions. This is the core abstract syntax
    representation of our language. Everything is unified as a single GADT
    to allow for higher-order types. *)
type _ ex =
  (* Variables. *)

  | Vari : 'a ex variable                              -> 'a ex
  (** Variables (of some sort). *)

  (* Higher order stuff. *)

  | HFun : ('a ex, 'b ex) lbinder                      -> ('a -> 'b) ex
  (** Higher-order function (e.g. parametric type). *)
  | HApp : ('a -> 'b) ex loc * 'a ex loc               -> 'b ex
  (** Corresponding higher-order application. *)

  (* Proposition constructors. *)

  | Func : p ex loc * p ex loc                         -> p ex
  (** Arrow type. *)
  | Prod : (pos * p ex loc) M.t                        -> p ex
  (** Product (or record) type. *)
  | DSum : (pos * p ex loc) M.t                        -> p ex
  (** Disjoint sum type. *)
  | Univ : ('a ex, p ex) lbinder                       -> p ex
  (** Universal quantification (e.g. polymorphism). *)
  | Exis : ('a ex, p ex) lbinder                       -> p ex
  (** Existential quantification (e.g. type abstraction). *)
  | FixM : o ex loc * (p ex, p ex) lbinder             -> p ex
  (** Inductive type with an ordinal size. *)
  | FixN : o ex loc * (p ex, p ex) lbinder             -> p ex
  (** Coinductive type with an ordinal size. *)
  | Memb : t ex loc * p ex loc                         -> p ex
  (** Membership type. *)
  | Rest : p ex loc * (t ex loc * bool * t ex loc)     -> p ex
  (** Restriction type. *)

  (* Value constructors. *)

  | LAbs : p ex loc option * (v ex, t ex) lbinder      -> v ex
  (** Lambda abstraction. *)
  | Cons : M.key loc * v ex loc                        -> v ex
  (** Constructor with exactly one argument. *)
  | Reco : (pos * v ex loc) M.t                        -> v ex
  (** Record (i.e. tuple with named fields). *)
  | Scis :                                                v ex
  (** PML scisors. *)

  (* Term constructors. *)

  | Valu : v ex loc                                    -> t ex
  (** Value as a term. *)
  | Appl : t ex loc * t ex loc                         -> t ex
  (** Application. *)
  | MAbs : (s ex, t ex) lbinder                        -> t ex
  (** Mu abstraction. *)
  | Name : s ex loc * t ex loc                         -> t ex
  (** Named term. *)
  | Proj : v ex loc * M.key loc                        -> t ex
  (** Record projection. *)
  | Case : v ex loc * (pos * (v ex, t ex) lbinder) M.t -> t ex 
  (** Case analysis. *)
  | FixY : t ex loc * v ex loc                         -> t ex
  (** Fixpoint combinator. *)

  (* Stack constructors. *)

  | Epsi :                                                s ex
  (** Empty stack. *)
  | Push : v ex loc * s ex loc                         -> s ex
  (** Value pushed on a stack. *)
  | Fram : t ex loc * s ex loc                         -> s ex
  (** Stack frame. *)

  (* Ordinal constructors. *)

  | Conv :                                                o ex
  (** Maximal ordinal. *)
  | Succ : o ex loc                                    -> o ex
  (** Successor of an ordinal. *)

  (* Type annotations. *)

  | DPrj : t ex loc * string loc                       -> p ex
  (** Dot projection. *)
  | VTyp : v ex loc * p ex loc                         -> v ex
  (** Type coercion on a term. *)
  | TTyp : t ex loc * p ex loc                         -> t ex
  (** Type coercion on a term. *)
  | VLam : (p ex, v ex) lbinder                        -> v ex
  (** Type abstraction on a value. *)
  | TLam : (p ex, v ex) lbinder                        -> t ex
  (** Type abstraction on a term. *)

  (* Special constructors. *)

  | ITag : int                                         -> 'a ex
  (** Integer tag (usuful for comparision). *)
  | VWit : (v ex, t ex) lbinder * p ex loc * p ex loc  -> v ex
  (** Value witness (a.k.a. epsilon). *)
  | SWit : (s ex, t ex) lbinder * p ex loc             -> s ex
  (** Stack witness (a.k.a. epsilon). *)
  | UWit : t ex loc * ('a ex, p ex) lbinder            -> 'a ex
  (** Universal quantifier witness (a.k.a. epsilon). *)
  | EWit : t ex loc * ('a ex, p ex) lbinder            -> 'a ex
  (** Existential quantifier witness (a.k.a. epsilon). *)
  | UVar : 'a ex loc option ref                        -> 'a ex
  (** Unification variable. *)
  (* TODO add MuRec and NuRec *)

type ordinal = o ex loc (** Type of ordinals. *)
type prop    = p ex loc (** Type of types.    *)
type value   = v ex loc (** Type of values.   *)
type term    = t ex loc (** Type of terms.    *)
type stack   = s ex loc (** Type of stacks.   *)
