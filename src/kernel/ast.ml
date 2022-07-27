(** Abstract syntax tree. This module defined the internal representation of
    PML's programs and higher-order type. *)

open Extra
open Bindlib
open Ptr
open Sorts
open Pos

module UTimed = Effect.UTimed
module M = Map.Make(String)
module A = Assoc

(** {6 Main abstract syntax tree type} *)

(** lazy type constructor reuses application, lambda and function type,
    anotated with the Lazy constant. In this case, argument is always unit *)
type laz = NoLz | Lazy

(** the hint for the proof checkee *)
type 'a hint =
          | Eval   (** try to use eval before adding the term in the pool.
                       if the term is not closed, proceed as usual. *)
          | Sugar (** indicate terms of the form "use t" or "show t"
                      where the term can be replaced by unit *)
          | Close of bool * 'a list (** close or open a definition locally *)
          | LSet of set_param (** local setting of a parameter *)
          | Auto of bool (** hint to turn on/off the use of auto.  used by
                            auto_prove only to have the recursive call
                            whre we want, see Typing.auto_prove code *)

and set_param =
  | Alvl of int * int
  | Logs of string
  | Keep of bool

(** Type of (well-sorted) expressions, which is the core PML abstract syntax
    representation. Everything is unified as a single GADT as  the  language
    provides higher-order types. *)
type _ ex =
  (* Variables. *)

  | Vari : 'a sort * 'a var                          -> 'a ex
  (** Variables (of some sort). *)

  (* Higher order stuff. *)

  | HFun : 'a sort * 'b sort * ('a, 'b) bndr         -> ('a -> 'b) ex
  (** Higher-order function. *)
  | HApp : 'a sort * ('a -> 'b) ex loc * 'a ex loc   -> 'b ex
  (** Corresponding higher-order application. *)
  | HDef : 'a sort * 'a expr                         -> 'a ex
  (** Definition of an expression. *)

  (* Proposition constructors. *)

  | Func : Effect.t * p ex loc * p ex loc * laz      -> p  ex
  (** Arrow type. *)
  | Prod : (pos * p ex loc) A.t               -> p  ex
  (** Product (or record) type. *)
  | DSum : (pos * p ex loc) A.t               -> p  ex
  (** Disjoint sum type. *)
  | Univ : 'a sort * ('a, p) bndr                    -> p  ex
  (** Universal quantification. *)
  | Exis : 'a sort * ('a, p) bndr                    -> p  ex
  (** Existential quantification. *)
  | FixM : 'a sort * o ex loc * ('a, 'a) bndr *
                                   ('a,'b) fix_args  -> 'b ex
  (** Inductive type with an ordinal size. *)
  | FixN : 'a sort * o ex loc * ('a, 'a) bndr *
                                   ('a,'b) fix_args  -> 'b ex
  (** Coinductive type with an ordinal size. *)
  | Memb : t ex loc * p ex loc                       -> p  ex
  (** Membership type. *)
  | Rest : p ex loc * rel                            -> p  ex
  (** Restriction type. *)
  | Impl : rel * p ex loc                            -> p  ex
  (** Conditional implication. *)

  (* Value constructors. *)

  | LAbs : p ex loc option * (v, t) bndr * laz       -> v  ex
  (** Lambda abstraction. λx.t *)
  | Cons : A.key loc * v ex loc                      -> v  ex
  (** Constructor with exactly one argument. *)
  | Reco : (pos * v ex loc) A.t                      -> v  ex
  (** Record. *)
  | Scis :                                              v  ex
  (** PML scisors. *)
  | VDef : value                                     -> v  ex
  (** Definition of a value. *)
  | VPtr : v_ptr                                     -> v  ex
  (** Pointer in the pool. *)
  | CPsi                                             : (v -> v) ex

  (* Term constructors. *)

  | Valu : v ex loc                                  -> t  ex
  (** Value as a term. *)
  | Appl : t ex loc * t ex loc * laz                 -> t  ex
  (** Application. *)
  | FixY : (t,  v) bndr                              -> t  ex
  (** Fixpoint combinator Y(x.v). *)
  | MAbs : (s, t) bndr                               -> t  ex
  (** Mu abstraction. *)
  | Name : s ex loc * t ex loc                       -> t  ex
  (** Named term. *)
  | Proj : v ex loc * A.key loc                      -> t  ex
  (** Record projection. *)
  | Case : v ex loc * (pos * (v, t) bndr) A.t        -> t  ex
  (** Case analysis. *)
  | Prnt : string                                    -> t  ex
  (** Printing instruction. *)
  | TPtr : ptr                                       -> t  ex
  (** Pointer in the pool. *)
  | Repl : t ex loc * t ex loc                       -> t  ex
  (** Triger totality by type rule *)
  | Delm : t ex loc                                  -> t  ex
  (** Hint for the proof checker *)
  | Hint : value hint * t ex loc                     -> t  ex
  (** Clock *)
  | Clck : v ex loc                                  -> t ex
  (** second member of the enumaration by the clock *)
  (* Ordinal constructors. *)

  | Conv :                                              o  ex
  (** Convergent ordinal. *)
  | Succ : o ex loc                                  -> o  ex
  (** Successor of an ordinal. *)
  | OWMu : (owit, string) eps                        -> o ex
  (** Ordinal mu witness. *)
  | OWNu : (owit, string) eps                        -> o  ex
  (** Ordinal nu witness. *)
  | OSch : int * o ex loc option * seps              -> o  ex
  (** Ordinal schema witness. *)
  | ESch : 'a sort * int * seps                      -> 'a  ex
  (** Expr schema witness. *)

  (* Type annotations. *)

  | Coer : 'a v_or_t * 'a ex loc * p ex loc          -> 'a ex
  (** Type coercion on a value or a term. *)
  | Such : 'a v_or_t * 'b desc * ('a,'b) such_t      -> 'a ex
  (** Extraction of witness by pattern-matching. *)
  | Chck : 'a v_or_t * v ex loc * p ex loc * 'a ex loc -> 'a ex
  (** Adding a subtyping to the hypothesis *)

  (* Special constructors. *)

  | ITag : 'a sort * int                             -> 'a ex
  (** Integer tag (used for hash of binder only). *)
  | VWit : (vwit, string) eps                        -> v  ex
  (** Value witness. *)
  | SWit : (swit, string) eps                        -> s  ex
  (** Stack witness. *)
  | UWit : ('a qwit, string) eps                     -> 'a ex
  (** Universal quantifier witness. *)
  | EWit : ('a qwit, string) eps                     -> 'a ex
  (** Existential quantifier witness. *)
  | UVar : 'a sort * 'a uvar                         -> 'a ex
  (** Unification variable. *)
  | Goal : 'a sort * string                          -> 'a ex

and (_,_) fix_args =
  | Nil : ('a, 'a) fix_args
  | Cns : 'a ex loc * ('b,'a -> 'c) fix_args -> ('b, 'c) fix_args

(** This is a structure to represent hash consed epsilon.
    See epsilon.ml for more comments *)
and ('a,'b) eps =
  { hash : int ref
  (** Hash of this epsilon. *)
  ; name : 'b
  (** Name, for printing the epsilons. *)
  ; vars : s_elt list ref
  (** List of unifiation variables used. *)
  ; refr : unit -> unit
  (** Refresh the epsilon on unificalion variables instanciation. *)
  ; valu : 'a ref
  (** Value of the epsilon. *)
  ; pure : bool Lazy.t ref
  (** Purity means using only intuitionistic (a.k.a. total) arrows. It must be
      lazy, otherwise we would infer total arrows for every arrows used inside
      epsilons.  Using laziness,  we only force the arrow to be total when the
      purity of the epsilon is required.  A reference must be used because the
      value should be updated on unification variables are instanciation. *)
  }

and seps = (schema, string array * string array) eps
and vwit = (v, t) bndr * p ex loc * p ex loc
and 'a qwit = 'a sort * t ex loc * ('a, p) bndr
and owit = o ex loc * t ex loc * (o, p) bndr
and swit = (s, t) bndr * p ex loc

and s_elt = U : 'a sort * 'a uvar -> s_elt

and rel =
  | Equiv of (t ex loc * bool * t ex loc)
  (** Equivalence between terms. *)
  | NoBox of v ex loc
  (** Value that are not Box, i.e. real value *)

and ('a,'b) such_t =
  { opt_var : such_var
  ; binder  : ('b, p ex loc * 'a ex loc) bseq }

and such_var =
  | SV_None :             such_var
  | SV_Valu : v ex loc -> such_var
  | SV_Stac : s ex loc -> such_var

and (_,_) bseq =
  | BLast : 'a sort * ('a ex, 'r          ) binder -> ('a     , 'r) bseq
  | BMore : 'a sort * ('a ex, ('b,'r) bseq) binder -> ('a * 'b, 'r) bseq

and 'a expr =
  { expr_name : strloc
  ; expr_def  : 'a ex loc
  ; expr_hash : int }

and value =
  { value_name : strloc
  ; value_orig : t ex loc
  ; value_type : p ex loc
  ; value_eval : e_valu
  ; value_eras : v ex loc
  ; value_clos : bool Timed.tref
  ; value_hash : int }

and fix_schema =
  { fsch_index : Scp.index (** index of the schema in the call graph *)
  ; fsch_judge : (t,v) bndr * (o ex, p ex loc) mbinder (** judgement *)
  ; fsch_safe  : bool (** do we prove termination *) }
  (* NOTE: [sch_judge = (vb,mob)] represents "λx.Y(λr.t, x) : a" where
     [mob] corresponds to "λr.t" and "mob" corresponds to "a", which is
     the only part of the judgment which can contain parameters. *)

and sbndr =
  | Cst : p ex loc * p ex loc -> sbndr
  | Bnd : 'a sort * ('a ex, sbndr) binder -> sbndr

and sub_schema =
  { ssch_index : Scp.index (** index of the schema in the call graph *)
  ; ssch_relat : (int * int) list (** relation between ordinals:
                                      j > i && j > 0, i and j being
                                      indexes in the mbinder below *)
  ; ssch_judge : (o ex, sbndr) mbinder (** judgement *) }

and schema =
  | FixSch of fix_schema
  | SubSch of sub_schema

and fix_specialised =
  { fspe_param : o ex loc array
  ; fspe_judge : (t,v) bndr * p ex loc }

and sub_specialised =
  { sspe_param : o ex loc array
  ; sspe_relat : (o ex loc * o ex loc) list
  ; sspe_judge : p ex loc * p ex loc }

(** Type of unification variables. *)
and 'a uvar =
  { uvar_key : int              (* a unique id *)
  ; uvar_val : 'a uvar_val ref  (* The value of the variable, see below *)
  ; uvar_pur : bool ref }       (* We set it to true when the value must be
                                   pure i.e. using only total arrows *)

and 'a uvar_val =
  | Set   of 'a ex loc
  (** The value of the unification variable when set *)
  | Unset of (unit -> unit) list
  (** When a unification variable is not set, we can register a list of
      functions to call on its instantiation. Currently, this is used to
      rehash epsilons using the unification variables. *)

(** {6 Types and functions related to binders and variables.} *)

(** Type of a (bindlib) variable.
    @see <https://www.lama.univ-savoie.fr/~raffalli/bindlib.html> bindlib *)
and 'a var = 'a ex Bindlib.var

(** Type of a (bindlib) binder with support for positions.
    @see <https://www.lama.univ-savoie.fr/~raffalli/bindlib.html> bindlib *)
and ('a, 'b) bndr = pos * ('a ex, 'b ex loc) binder

(** Type of an expression in a (bindlib) box.
    @see <https://www.lama.univ-savoie.fr/~raffalli/bindlib.html> bindlib *)
and 'a ebox = 'a ex loc box

and e_lazy = Frz of e_term | Val of e_valu

and e_valu =
  | VVari of e_valu Bindlib.var
  | VLAbs of (e_valu, e_term) binder
  | VLazy of e_lazy ref
  | VCons of string * e_valu
  | VReco of e_valu A.t
  | VVdef of value
  | VScis
and  e_term =
  | TVari of e_term Bindlib.var
  | TValu of e_valu
  | TAppl of e_term * e_term
  | TFrce of e_term
  | TFixY of (e_term, e_valu) Bindlib.binder
  | TMAbs of (e_stac, e_term) Bindlib.binder
  | TName of e_stac * e_term
  | TProj of e_valu * string
  | TCase of e_valu * (e_valu, e_term) Bindlib.binder A.t
  | TPrnt of string
  | TClck of e_valu
and  e_stac =
  | SVari of e_stac Bindlib.var
  | SEpsi
  | SPush of e_valu * e_stac
  | SFram of e_term * e_stac

type any_sort = Sort : 'a sort           -> any_sort
type any_expr = Expr : 'a sort * 'a expr -> any_expr
type any_var  = AVar : 'a sort * 'a var  -> any_var

(** Sequence of functions to build and [bseq]. *)
type (_,_) fseq =
  | FLast : 'c sort * strloc * ('c var -> 'r box  ) -> ('c     , 'r) fseq
  | FMore : 'c sort * strloc * ('c var -> ('a,'r) fseq) -> ('c * 'a, 'r) fseq

(** Binder substitution function. *)
let bndr_subst : ('a, 'b) bndr -> 'a ex -> 'b ex loc =
  fun (_,b) t -> subst b t

(** Open a binder *)
let bndr_open : ('a, 'b) bndr -> 'a var * 'b ex loc =
  fun (_,b) -> unbind b
let bndr_term : ('a, 'b) bndr -> 'b ex loc =
  fun b -> snd (bndr_open b)
let bndr_open_in : ctxt -> ('a, 'b) bndr -> 'a var * 'b ex loc * ctxt =
  fun ctxt (_,b) -> unbind_in ctxt b

(** Obtain the name of a bound variable in the form of a located string. The
    position corresponds to the variable in binding position. *)
let bndr_name : ('a, 'b) bndr -> strloc =
  fun (p, b) -> Pos.in_pos p (binder_name b)

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

type vbox = v ebox    (** Value   box type. *)
type tbox = t ebox    (** Term    box type. *)
type sbox = s ebox    (** Stack   box type. *)
type pbox = p ebox    (** Type    box type. *)
type obox = o ebox    (** Ordinal box type. *)

type ('a,'b) fbox = ('a,'b) fix_args box   (** boxed args for FixM and FixN *)

(** {6 Smart constructors} *)

let mk_free : 'a sort -> 'a var -> 'a ex =
  fun s x -> Vari(s, x)

(** {5 Higher order stuff} *)

let vari : type a. pos -> a var -> a ex loc box =
  fun p x -> box_apply (fun x -> Pos.in_pos p x) (box_var x)

let hfun : type a b. pos -> a sort -> b sort -> strloc -> (a var -> b ebox)
             -> (a -> b) ebox =
  fun p sa sb x f ->
    let v = new_var (mk_free sa) x.elt in
    let b = bind_var v (f v) in
    box_apply (fun b -> Pos.in_pos p (HFun(sa, sb, (x.pos, b)))) b

let happ : type a b. pos -> a sort -> (a -> b) ebox -> a ebox -> b ebox =
  fun p s -> box_apply2 (fun f a -> Pos.in_pos p (HApp(s,f,a)))

(** {5 Value constructors} *)

let v_vari : pos -> vvar -> vbox = vari

let labs : pos -> laz -> pbox option -> strloc -> (vvar -> tbox) -> vbox =
  fun p l ao x f ->
    let v = new_var (mk_free V) x.elt in
    let b = bind_var v (f v) in
    box_apply2 (fun ao b -> Pos.in_pos p (LAbs(ao, (x.pos, b), l)))
               (box_opt ao) b

let lvabs : pos -> laz -> pbox option -> vvar -> tbox -> vbox =
  fun p l ao v t ->
    box_apply2 (fun ao b -> Pos.in_pos p (LAbs(ao, (no_pos, b), l)))
               (box_opt ao) (bind_var v t)

let cons : pos -> strloc -> vbox -> vbox =
  fun p c -> box_apply (fun v -> Pos.in_pos p (Cons(c,v)))

let reco : pos -> (pos * vbox) A.t -> vbox =
  fun p m ->
    let f (lpos, v) = box_apply (fun v -> (lpos, v)) v in
    box_apply (fun m -> Pos.in_pos p (Reco(m))) (A.map_box f m)

let unit_reco = reco no_pos A.empty
let scis : pos -> vbox =
  fun pos -> box (Pos.in_pos pos Scis)

(** {5 Term constructors} *)

let t_vari : pos -> tvar -> tbox = vari

let valu : pos -> vbox -> tbox =
  fun p -> box_apply (fun v -> Pos.in_pos p (Valu v))

let idt_valu : (v, t) bndr =
  let x = new_var (mk_free V) "x" in
  (no_pos, Bindlib.unbox (Bindlib.bind_var x (valu no_pos (vari no_pos x))))
let appl : pos -> laz -> tbox -> tbox -> tbox =
  fun p l -> box_apply2 (fun t u -> Pos.in_pos p (Appl(t,u,l)))

let hint : pos -> value hint -> tbox -> tbox =
  fun p h -> box_apply (fun t -> Pos.in_pos p (Hint(h,t)))

let hint : pos -> value hint -> tbox -> tbox =
  fun p h -> box_apply (fun t -> Pos.in_pos p (Hint(h,t)))

let clck : pos -> vbox -> tbox =
  fun p -> box_apply (fun v -> Pos.in_pos p (Clck v))

let cpsi : pos -> (v -> v) ex loc box =
  fun p -> box (Pos.in_pos p CPsi)

let sequ : pos -> tbox -> tbox -> tbox =
  fun p t u ->
    appl p NoLz
      (valu no_pos (labs no_pos NoLz None (Pos.none "_") (fun _ -> u)))
      t

let mabs : pos -> strloc -> (svar -> tbox) -> tbox =
  fun p x f ->
    let v = new_var (mk_free S) x.elt in
    let b = bind_var v (f v) in
    box_apply (fun b -> Pos.in_pos p (MAbs(x.pos, b))) b

let name : pos -> sbox -> tbox -> tbox =
  fun p -> box_apply2 (fun s t -> Pos.in_pos p (Name(s,t)))

let proj : pos -> vbox -> strloc -> tbox =
  fun p v l -> box_apply (fun v -> Pos.in_pos p (Proj(v,l))) v

let case : pos -> vbox -> (pos * strloc * (vvar -> tbox)) A.t -> tbox =
  fun p v m ->
  let f (cpos, x, f) =
      let v = new_var (mk_free V) x.elt in
      let b = bind_var v (f v) in
      box_apply (fun b -> (cpos, (x.pos, b))) b
    in
    box_apply2 (fun v m -> Pos.in_pos p (Case(v,m))) v (A.map_box f m)

let fixy : pos -> strloc -> (tvar -> vbox) -> tbox =
  fun p x f ->
    let v = new_var (mk_free T) x.elt in
    let b = bind_var v (f v) in
    box_apply (fun b -> Pos.in_pos p (FixY(x.pos, b))) b

let prnt : pos -> string -> tbox =
  fun p s -> box (Pos.in_pos p (Prnt(s)))

let repl : pos -> tbox -> tbox -> tbox option -> tbox =
  fun p t u b ->
    let u = match b with
      | None -> u
      | Some b -> sequ no_pos b u
    in
    box_apply2 (fun t u -> Pos.in_pos p (Repl(t,u))) t u

let delm : pos -> tbox -> tbox =
  fun p -> box_apply (fun u -> Pos.in_pos p (Delm(u)))

(** {5 Type annotation constructors} *)

let coer : type a. pos -> a v_or_t -> a ebox -> pbox -> a ebox =
  fun p t -> box_apply2 (fun e a -> Pos.in_pos p (Coer(t,e,a)))

let such : type a b. pos -> a v_or_t -> b desc -> such_var box
           -> (b, prop * a ex loc) fseq -> a ebox =
  let rec aux : type a c. (c, p ex loc * a ex loc) fseq
      -> (c, prop * a ex loc) bseq box = fun fs ->
    match fs with
    | FLast(s,x,f) ->
        let v = new_var (mk_free s) x.elt in
        box_apply (fun b -> BLast(s,b)) (bind_var v (f v))
    | FMore(s,x,f) ->
        let v = new_var (mk_free s) x.elt in
        let b = bind_var v (aux (f v)) in
        box_apply (fun b -> BMore(s,b)) b
  in
  fun p t d sv f ->
    let fn sv b = Pos.in_pos p (Such(t,d,{opt_var = sv; binder = b})) in
    box_apply2 fn sv (aux f)

let cst : pbox -> pbox -> sbndr box =
  fun a b -> box_apply2 (fun a b -> Cst(a,b)) a b

let bnd : type a.a sort -> string -> (a var -> sbndr box) -> sbndr box =
  fun s x f ->
  let v = new_var (mk_free s) x in
  let b = bind_var v (f v) in
  box_apply (fun b -> Bnd(s,b)) b

let bnd_var : type a.a sort -> a var -> sbndr box -> sbndr box =
  fun s v f ->
  let b = bind_var v f in
  box_apply (fun b -> Bnd(s,b)) b

let chck =
  fun p s v a f ->
  box_apply3 (fun v a f -> Pos.in_pos p (Chck(s,v,a,f))) v a f

let pset : pos -> set_param -> tbox -> tbox =
  fun p sp t ->
    let fn t = Pos.in_pos p (Hint(LSet(sp),t)) in
    box_apply fn t

let sv_none : such_var box =
  box SV_None

let sv_valu : vbox -> such_var box =
  box_apply (fun v -> SV_Valu(v))

let sv_stac : sbox -> such_var box =
  box_apply (fun s -> SV_Stac(s))

(** {5 Stack constructors} *)

let s_vari : pos -> svar -> sbox = vari

(** {5 Proposition constructors} *)

let p_vari : pos -> pvar -> pbox = vari

let func : pos -> Effect.t -> laz -> pbox -> pbox -> pbox =
  fun p t l -> box_apply2 (fun a b -> Pos.in_pos p (Func(t,a,b,l)))

let prod : pos -> (pos * pbox) A.t -> pbox =
  fun p m ->
    let f (lpos, a) = box_apply (fun a -> (lpos, a)) a in
    box_apply (fun m -> Pos.in_pos p (Prod(m))) (A.map_box f m)

let unit_prod = prod no_pos A.empty

let dsum : pos -> (pos * pbox) A.t -> pbox =
  fun p m ->
    let f (lpos, a) = box_apply (fun a -> (lpos, a)) a in
    box_apply (fun m -> Pos.in_pos p (DSum(m))) (A.map_box f m)

let univ : type a. pos -> strloc -> a sort -> (a var -> pbox) -> pbox =
  fun p x s f ->
    let v = new_var (mk_free s) x.elt in
    let b = bind_var v (f v) in
    box_apply (fun b -> Pos.in_pos p (Univ(s, (x.pos, b)))) b

let bottom : prop =
  unbox (univ no_pos (Pos.none "x") P (fun x -> p_vari no_pos x))

let exis : type a. pos -> strloc -> a sort -> (a var -> pbox) -> pbox =
  fun p x s f ->
    let v = new_var (mk_free s) x.elt in
    let b = bind_var v (f v) in
    box_apply (fun b -> Pos.in_pos p (Exis(s, (x.pos, b)))) b

let top : prop =
  unbox (exis no_pos (Pos.none "x") P (fun x -> p_vari no_pos x))

let nil : type a. unit -> (a,a) fbox = fun () -> box Nil

let cns : type a b c. a ebox -> (b,a->c) fbox -> (b,c) fbox =
  fun e l ->
    box_apply2 (fun e l -> Cns(e, l)) e l

let fixm : type a b. pos -> a sort -> obox -> strloc ->
                (a var ->  a ebox) -> (a,b) fbox -> b ebox =
  fun p s o x f l ->
    let v = new_var (mk_free s) x.elt in
    let b = bind_var v (f v) in
    box_apply3 (fun o b l -> Pos.in_pos p (FixM(s, o, (x.pos, b), l))) o b l

let fixn : type a b. pos -> a sort -> obox -> strloc ->
                (a var ->  a ebox) -> (a,b) fbox -> b ebox =
  fun p s o x f l ->
    let v = new_var (mk_free s) x.elt in
    let b = bind_var v (f v) in
    box_apply3 (fun o b l -> Pos.in_pos p (FixN(s, o, (x.pos, b), l))) o b l

let memb : pos -> tbox -> pbox -> pbox =
  fun p -> box_apply2 (fun t a -> Pos.in_pos p (Memb(t,a)))

let rest : pos -> pbox -> rel box -> pbox =
  fun p -> box_apply2 (fun a c -> Pos.in_pos p (Rest(a,c)))

let impl : pos -> rel box -> pbox -> pbox =
  fun p -> box_apply2 (fun c a -> Pos.in_pos p (Impl(c,a)))

(** subtyping as proposition *)
let subt : pos -> pbox -> pbox -> pbox = fun p a b ->
  univ p (none "x") V (fun x ->
      let x = valu no_pos (vari no_pos x) in
      func p Effect.bot NoLz (memb no_pos x a) (memb no_pos x b))

(** {5 Condition constructors} *)

let equiv : tbox -> bool -> tbox -> rel box =
  fun t b u ->
    box_apply2 (fun t u -> Equiv(t,b,u)) t u

let nobox : vbox -> rel box =
  box_apply (fun v -> NoBox(v))

(** {5 Ordinal constructors} *)

let o_vari : pos -> ovar -> obox = vari

let conv : pos -> obox =
  fun p -> box (Pos.in_pos p Conv)

let succ : pos -> obox -> obox =
  fun p -> box_apply (fun o -> Pos.in_pos p (Succ(o)))

let goal : type a. pos -> a sort -> string -> a ex loc box =
  fun p s str -> box (Pos.in_pos p (Goal(s,str)))

(** {5 syntactic sugars} *)

(** Syntactic sugar for projections of a term. *)
let t_proj : pos -> tbox -> (pos * strloc) list -> tbox =
  fun p t ls ->
    if ls = [] then t else
    let rec fn ls =
      match ls with
      | []    -> assert false
      | [(p,l)]   ->
         let f x = proj p (v_vari no_pos x) l in
         valu p (labs p NoLz None (Pos.none "x") f)
      | (p,l)::ls ->
         let f x = appl p NoLz (fn ls) (proj p (v_vari no_pos x) l) in
         valu p (labs p NoLz None (Pos.none "x") f)
    in
    appl p NoLz (fn ls) t

let x_proj : pos -> t ex loc -> strloc -> t ex loc = fun p t l ->
  match t.elt with
  | Valu v -> Pos.in_pos p (Proj(v,l))
  | _      -> unbox (t_proj p (box t) [p,l])

(** Syntactic sugar to build redexes *)
let rec redexes : pos -> (vvar * tbox) list -> tbox -> tbox =
  fun pos l t -> match l with
  | [] -> t
  | (v,t0)::l ->
     redexes pos l
       (appl pos NoLz (valu no_pos (lvabs no_pos NoLz None v t)) t0)

(** Syntactic sugar for strict product type. *)
let proj_name l =
  if l = "" then "x"
  else if l.[0] >= '0' && l.[0] <= '9' then "x"^l
  else l

let strict_prod : pos -> (pos * pbox) A.t -> pbox =
  fun p m ->
    let fn env =
      reco no_pos (A.mapi (fun l _ -> (no_pos, List.assoc l env)) m)
    in
    let rec build env ls =
      match ls with
      | []    -> memb no_pos (valu no_pos (fn env)) (prod p m)
      | l::ls -> let fn (x:vvar) = build ((l, vari no_pos x) :: env) ls in
                 exis no_pos (Pos.none (proj_name l)) V fn
    in
    build [] (List.map fst (A.bindings m))

(** produce t = true *)
let eq_true : pos -> tbox -> pbox =
  fun _loc t ->
    let true_ = cons no_pos (Pos.none "true") (reco no_pos A.empty) in
    let cond = equiv t true (valu no_pos true_) in
    rest _loc (strict_prod no_pos A.empty) cond

(** {5 Useful types} *)

let nat : pbox =
  fixm no_pos P (conv no_pos) (Pos.none "nat") (fun r ->
      let m = A.add "Zero" (no_pos, strict_prod no_pos A.empty)
                (A.add "S" (no_pos, vari no_pos r) A.empty)
      in
      dsum no_pos m) (box Nil)

let pair a b : pbox =
  let m = A.add "1" (no_pos, a) (A.add "2" (no_pos, b) A.empty) in
  strict_prod no_pos m

let ac_right a v =
  unbox (exis no_pos (Pos.none "n") V (fun n ->
             let n = vari no_pos n in
             let psi_n = valu no_pos (happ no_pos V (cpsi no_pos) n) in
             rest no_pos (memb no_pos (valu no_pos n) nat)
               (equiv psi_n true (valu no_pos (box v)))))

(** {5 useful functions} *)

let rec is_scis : type a. a ex loc -> bool =
  fun e ->
    match e.elt with
    | Scis        -> true
    | Valu(v)     -> is_scis v
    | LAbs(_,f,_) -> (* because of sugar like show ...; 8< *)
                     is_scis (bndr_term f)
    | _           -> false

(*
let build_v_fixy : (v,t) bndr -> valu = fun b ->
  let f x = box_apply (fun x -> Pos.none (FixY(b,x,None))) (v_vari None x) in
  unbox (labs None None (Pos.none "x") f)

let build_t_fixy : (v,t) bndr -> term = fun b ->
  Pos.none (Valu(build_v_fixy b))
 *)

let rec bseq_open: type a b. (a, prop * b) bseq -> b = fun seq ->
  match seq with
  | BLast(s,f) -> snd (snd (unbind f))
  | BMore(s,f) -> bseq_open (snd (unbind f))

let rec tail_sort : type a b. a sort -> (a, b) fix_args -> b sort =
  fun s l -> match l with
            | Nil -> s
            | Cns(_,l) ->
               match tail_sort s l with
               | F(_,s) -> s

let rec sort : type a. a ex loc -> a sort * a ex loc = fun e ->
  match e.elt with
  | HDef(s,_)       -> (s, e)
  | HApp(d,u,v)     -> let (F(_,s),_) = sort u in (s,e)
  | HFun(d,c,r)     -> (F(d, c), e)
  | UWit(w)         -> let (s,_,_) = !(w.valu) in (s, e)
  | EWit(w)         -> let (s,_,_) = !(w.valu) in (s, e)
  | UVar(s,_)       -> (s,e)
  | ITag(s,_)       -> (s,e)
  | Goal(s,_)       -> (s,e)

  | Func _          -> (P,e)
  | Prod _          -> (P,e)
  | DSum _          -> (P,e)
  | Univ _          -> (P,e)
  | Exis _          -> (P,e)
  | FixM (s,_,_,l)  -> (tail_sort s l,e)
  | FixN (s,_,_,l)  -> (tail_sort s l,e)
  | Memb _          -> (P,e)
  | Rest _          -> (P,e)
  | Impl _          -> (P,e)

  | VWit _          -> (V,e)
  | LAbs _          -> (V,e)
  | Cons _          -> (V,e)
  | Reco _          -> (V,e)
  | Scis            -> (V,e)
  | VDef _          -> (V,e)
  | Coer(VoT_V,_,_) -> (V,e)
  | Such(VoT_V,_,_) -> (V,e)
  | Chck(VoT_V,_,_,_)-> (V,e)
  | VPtr _          -> (V,e)
  | CPsi            -> (F(V,V),e)

  | Valu _          -> (T,e)
  | Appl _          -> (T,e)
  | MAbs _          -> (T,e)
  | Name _          -> (T,e)
  | Proj _          -> (T,e)
  | Case _          -> (T,e)
  | FixY _          -> (T,e)
  | Prnt _          -> (T,e)
  | Coer(VoT_T,_,_) -> (T,e)
  | Such(VoT_T,_,_) -> (T,e)
  | Chck(VoT_T,_,_,_)-> (T,e)
  | TPtr _          -> (T,e)
  | Repl(_,_)       -> (T,e)
  | Delm _          -> (T,e)
  | Hint _          -> (T,e)
  | Clck _          -> (T,e)

  | SWit _          -> (S,e)

  | Conv            -> (O,e)
  | Succ _          -> (O,e)
  | OWMu _          -> (O,e)
  | OWNu _          -> (O,e)
  | OSch _          -> (O,e)
  | ESch(s,_,_)     -> (s,e)

  | Vari(s,_)       -> (s,e)

type fprint =
      { mutable f : 'a. out_channel -> 'a ex loc -> unit }

let fprint = { f = fun ch x -> assert false }
let rec apply_args : type a b. a ex loc -> (a, b) fix_args -> b ex loc =
  fun f l ->
    match l with Nil -> f
               | Cns(a,l) -> let (s,a) = sort a in
                             Pos.none (HApp(s, apply_args f l, a))

let unroll_FixM s o f l = apply_args (bndr_subst f (FixM(s,o,f,Nil))) l
let unroll_FixN s o f l = apply_args (bndr_subst f (FixN(s,o,f,Nil))) l

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
  let f x = valu no_pos (vari no_pos x) in
  let id = (no_pos, Pos.none "x", f) in
  unbox (case no_pos (box v) (A.singleton c id))
