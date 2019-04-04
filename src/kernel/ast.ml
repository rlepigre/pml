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

  | Func : Effect.t * p ex loc * p ex loc            -> p  ex
  (** Arrow type. *)
  | Prod : (pos option * p ex loc) A.t               -> p  ex
  (** Product (or record) type. *)
  | DSum : (pos option * p ex loc) A.t               -> p  ex
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

  | LAbs : p ex loc option * (v, t) bndr * Effect.t  -> v  ex
  (** Lambda abstraction. λx.t *)
  | Cons : A.key loc * v ex loc                      -> v  ex
  (** Constructor with exactly one argument. *)
  | Reco : (popt * v ex loc) A.t                     -> v  ex
  (** Record. *)
  | Scis :                                              v  ex
  (** PML scisors. *)
  | VDef : value                                     -> v  ex
  (** Definition of a value. *)
  | VPtr : v_ptr                                     -> v  ex
  (** Pointer in the pool. *)

  (* Term constructors. *)

  | Valu : v ex loc                                  -> t  ex
  (** Value as a term. *)
  | Appl : t ex loc * t ex loc                       -> t  ex
  (** Application. *)
  | FixY : (t,  v) bndr                              -> t  ex
  (** Fixpoint combinator Y(x.v). *)
  | MAbs : (s, t) bndr                               -> t  ex
  (** Mu abstraction. *)
  | Name : s ex loc * t ex loc                       -> t  ex
  (** Named term. *)
  | Proj : v ex loc * A.key loc                      -> t  ex
  (** Record projection. *)
  | Case : v ex loc * (popt * (v, t) bndr) A.t       -> t  ex
  (** Case analysis. *)
  | Prnt : string                                    -> t  ex
  (** Printing instruction. *)
  | TPtr : ptr                                       -> t  ex
  (** Pointer in the pool. *)
  | Repl : t ex loc * t ex loc                       -> t  ex
  (** Triger totality by type rule *)
  | Delm : t ex loc                                  -> t  ex

  (* Ordinal constructors. *)

  | Conv :                                              o  ex
  (** Convergent ordinal. *)
  | Succ : o ex loc                                  -> o  ex
  (** Successor of an ordinal. *)
  | OWMu : (owit, string) eps                        -> o ex
  (** Ordinal mu witness. *)
  | OWNu : (owit, string) eps                        -> o  ex
  (** Ordinal nu witness. *)
  | OSch : int * o ex loc option * (schema, string array) eps
                                                     -> o  ex
  (** Ordinal schema witness. *)
  | ESch : 'a sort * int * (schema, string array) eps
                                                     -> 'a  ex
  (** Expr schema witness. *)

  (* Type annotations. *)

  | Coer : 'a v_or_t * 'a ex loc * p ex loc          -> 'a ex
  (** Type coercion on a value or a term. *)
  | Such : 'a v_or_t * 'b desc * ('a,'b) such_t      -> 'a ex
  (** Extraction of witness by pattern-matching. *)
  | PSet : set_param * 'a v_or_t * 'a ex loc         -> 'a ex
  (** Set auto lvl *)

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

and set_param =
  | Alvl of int * int
  | Logs of string
  | Keep of bool

(** {6 Types and functions related to binders and variables.} *)

(** Type of a (bindlib) variable.
    @see <https://www.lama.univ-savoie.fr/~raffalli/bindlib.html> bindlib *)
and 'a var = 'a ex Bindlib.var

(** Type of a (bindlib) binder with support for positions.
    @see <https://www.lama.univ-savoie.fr/~raffalli/bindlib.html> bindlib *)
and ('a, 'b) bndr = popt * ('a ex, 'b ex loc) binder

(** Type of an expression in a (bindlib) box.
    @see <https://www.lama.univ-savoie.fr/~raffalli/bindlib.html> bindlib *)
and 'a ebox = 'a ex loc box

and e_lazy = e_valu option ref

and e_valu =
  | VVari of e_valu Bindlib.var
  | VLAbs of (e_valu, e_term) binder * e_lazy option
  | VCons of string * e_valu
  | VReco of e_valu A.t
  | VVdef of value
  | VScis
and  e_term =
  | TVari of e_term Bindlib.var
  | TValu of e_valu
  | TAppl of e_term * e_term
  | TFixY of (e_term, e_valu) Bindlib.binder
  | TMAbs of (e_stac, e_term) Bindlib.binder
  | TName of e_stac * e_term
  | TProj of e_valu * string
  | TCase of e_valu * (e_valu, e_term) Bindlib.binder A.t
  | TPrnt of string
and  e_stac =
  | SVari of e_stac Bindlib.var
  | SEpsi
  | SPush of e_valu * e_stac
  | SFram of e_term * e_stac

type any_sort = Sort : 'a sort           -> any_sort
type any_expr = Expr : 'a sort * 'a expr -> any_expr

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

(** Obtain the name of a bound variable in the form of a located string. The
    position corresponds to the variable in binding position. *)
let bndr_name : ('a, 'b) bndr -> strloc =
  fun (p, b) -> Pos.make p (binder_name b)

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

let vari : type a. popt -> a var -> a ex loc box =
  fun p x -> box_apply (fun x -> Pos.make p x) (box_var x)

let hfun : type a b. popt -> a sort -> b sort -> strloc -> (a var -> b ebox)
             -> (a -> b) ebox =
  fun p sa sb x f ->
    let v = new_var (mk_free sa) x.elt in
    let b = bind_var v (f v) in
    box_apply (fun b -> Pos.make p (HFun(sa, sb, (x.pos, b)))) b

let happ : type a b. popt -> a sort -> (a -> b) ebox -> a ebox -> b ebox =
  fun p s -> box_apply2 (fun f a -> Pos.make p (HApp(s,f,a)))

(** {5 Value constructors} *)

let v_vari : popt -> vvar -> vbox = vari

let labs : popt -> pbox option -> strloc -> (vvar -> tbox) -> vbox =
  fun p ao x f ->
    let v = new_var (mk_free V) x.elt in
    let b = bind_var v (f v) in
    let t = Effect.create () in
    box_apply2 (fun ao b -> Pos.make p (LAbs(ao, (x.pos, b), t)))
               (box_opt ao) b

let lvabs : popt -> pbox option -> vvar -> tbox -> vbox =
  fun p ao v t ->
    let tot = Effect.create () in
    box_apply2 (fun ao b -> Pos.make p (LAbs(ao, (None, b), tot)))
               (box_opt ao) (bind_var v t)

let cons : popt -> strloc -> vbox -> vbox =
  fun p c -> box_apply (fun v -> Pos.make p (Cons(c,v)))

let reco : popt -> (popt * vbox) A.t -> vbox =
  fun p m ->
    let f (lpos, v) = box_apply (fun v -> (lpos, v)) v in
    box_apply (fun m -> Pos.make p (Reco(m))) (A.map_box f m)

let unit_reco = reco None A.empty
let scis : popt -> vbox =
  fun pos -> box (Pos.make pos Scis)

(** {5 Term constructors} *)

let t_vari : popt -> tvar -> tbox = vari

let valu : popt -> vbox -> tbox =
  fun p -> box_apply (fun v -> Pos.make p (Valu v))

let idt_valu : (v, t) bndr =
  let x = new_var (mk_free V) "x" in
  (None, Bindlib.unbox (Bindlib.bind_var x (valu None (vari None x))))

let appl : popt -> tbox -> tbox -> tbox =
  fun p -> box_apply2 (fun t u -> Pos.make p (Appl(t,u)))

let sequ : popt -> tbox -> tbox -> tbox =
  fun p t u ->
    appl p (valu None (labs None None (Pos.none "_") (fun _ -> u))) t

let mabs : popt -> strloc -> (svar -> tbox) -> tbox =
  fun p x f ->
    let v = new_var (mk_free S) x.elt in
    let b = bind_var v (f v) in
    box_apply (fun b -> Pos.make p (MAbs(x.pos, b))) b

let name : popt -> sbox -> tbox -> tbox =
  fun p -> box_apply2 (fun s t -> Pos.make p (Name(s,t)))

let proj : popt -> vbox -> strloc -> tbox =
  fun p v l -> box_apply (fun v -> Pos.make p (Proj(v,l))) v

let case : popt -> vbox -> (popt * strloc * (vvar -> tbox)) A.t -> tbox =
  fun p v m ->
  let f (cpos, x, f) =
      let v = new_var (mk_free V) x.elt in
      let b = bind_var v (f v) in
      box_apply (fun b -> (cpos, (x.pos, b))) b
    in
    box_apply2 (fun v m -> Pos.make p (Case(v,m))) v (A.map_box f m)

let fixy : popt -> strloc -> (tvar -> vbox) -> tbox =
  fun p x f ->
    let v = new_var (mk_free T) x.elt in
    let b = bind_var v (f v) in
    box_apply (fun b -> Pos.make p (FixY(x.pos, b))) b

let prnt : popt -> string -> tbox =
  fun p s -> box (Pos.make p (Prnt(s)))

let repl : popt -> tbox -> tbox -> tbox option -> tbox =
  fun p t u b ->
    let u = match b with
      | None -> u
      | Some b ->
         let fn x = sequ None b (valu None (vari None x)) in
         appl None (valu None (labs None None (Pos.none "res") fn)) u
    in
    box_apply2 (fun t u -> Pos.make p (Repl(t,u))) t u

let delm : popt -> tbox -> tbox =
  fun p -> box_apply (fun u -> Pos.make p (Delm(u)))

(** {5 Type annotation constructors} *)

let coer : type a. popt -> a v_or_t -> a ebox -> pbox -> a ebox =
  fun p t -> box_apply2 (fun e a -> Pos.make p (Coer(t,e,a)))

let such : type a b. popt -> a v_or_t -> b desc -> such_var box
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
    let fn sv b = Pos.make p (Such(t,d,{opt_var = sv; binder = b})) in
    box_apply2 fn sv (aux f)

let pset : type a. popt -> set_param -> a v_or_t -> a ebox -> a ebox =
  fun p sp sv t ->
    let fn t = Pos.make p (PSet(sp,sv,t)) in
    box_apply fn t

let sv_none : such_var box =
  box SV_None

let sv_valu : vbox -> such_var box =
  box_apply (fun v -> SV_Valu(v))

let sv_stac : sbox -> such_var box =
  box_apply (fun s -> SV_Stac(s))

(** {5 Stack constructors} *)

let s_vari : popt -> svar -> sbox = vari

(** {5 Proposition constructors} *)

let p_vari : popt -> pvar -> pbox = vari

let func : popt -> Effect.t -> pbox -> pbox -> pbox =
  fun p t -> box_apply2 (fun a b -> Pos.make p (Func(t,a,b)))

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
    let v = new_var (mk_free s) x.elt in
    let b = bind_var v (f v) in
    box_apply (fun b -> Pos.make p (Univ(s, (x.pos, b)))) b

let bottom : prop =
  unbox (univ None (Pos.none "x") P (fun x -> p_vari None x))

let exis : type a. popt -> strloc -> a sort -> (a var -> pbox) -> pbox =
  fun p x s f ->
    let v = new_var (mk_free s) x.elt in
    let b = bind_var v (f v) in
    box_apply (fun b -> Pos.make p (Exis(s, (x.pos, b)))) b

let top : prop = unbox (exis None (Pos.none "x") P (fun x -> p_vari None x))

let nil : type a. unit -> (a,a) fbox = fun () -> box Nil

let cns : type a b c. a ebox -> (b,a->c) fbox -> (b,c) fbox =
  fun e l ->
    box_apply2 (fun e l -> Cns(e, l)) e l

let fixm : type a b. popt -> a sort -> obox -> strloc ->
                (a var ->  a ebox) -> (a,b) fbox -> b ebox =
  fun p s o x f l ->
    let v = new_var (mk_free s) x.elt in
    let b = bind_var v (f v) in
    box_apply3 (fun o b l -> Pos.make p (FixM(s, o, (x.pos, b), l))) o b l

let fixn : type a b. popt -> a sort -> obox -> strloc ->
                (a var ->  a ebox) -> (a,b) fbox -> b ebox =
  fun p s o x f l ->
    let v = new_var (mk_free s) x.elt in
    let b = bind_var v (f v) in
    box_apply3 (fun o b l -> Pos.make p (FixN(s, o, (x.pos, b), l))) o b l

let memb : popt -> tbox -> pbox -> pbox =
  fun p -> box_apply2 (fun t a -> Pos.make p (Memb(t,a)))

let rest : popt -> pbox -> rel box -> pbox =
  fun p -> box_apply2 (fun a c -> Pos.make p (Rest(a,c)))

let impl : popt -> rel box -> pbox -> pbox =
  fun p -> box_apply2 (fun c a -> Pos.make p (Impl(c,a)))

(** {5 Condition constructors} *)

let equiv : tbox -> bool -> tbox -> rel box =
  fun t b u ->
    box_apply2 (fun t u -> Equiv(t,b,u)) t u

let nobox : vbox -> rel box =
  box_apply (fun v -> NoBox(v))

(** {5 Ordinal constructors} *)

let o_vari : popt -> ovar -> obox = vari

let conv : popt -> obox =
  fun p -> box (Pos.make p Conv)

let succ : popt -> obox -> obox =
  fun p -> box_apply (fun o -> Pos.make p (Succ(o)))

let goal : type a. popt -> a sort -> string -> a ex loc box =
  fun p s str -> box (Pos.make p (Goal(s,str)))

(** {5 syntactic sugars} *)

(** Syntactic sugar for projections of a term. *)
let t_proj : popt -> tbox -> (popt * strloc) list -> tbox =
  fun p t ls ->
    if ls = [] then t else
    let rec fn ls =
      match ls with
      | []    -> assert false
      | [(p,l)]   ->
         let f x = proj p (v_vari None x) l in
         valu p (labs p None (Pos.none "x") f)
      | (p,l)::ls ->
         let f x = appl p (fn ls) (proj p (v_vari None x) l) in
         valu p (labs p None (Pos.none "x") f)
    in
    appl p (fn ls) t

(** Syntactic sugar to build redexes *)
let rec redexes : pos option -> (vvar * tbox) list -> tbox -> tbox =
  fun pos l t -> match l with
  | [] -> t
  | (v,t0)::l ->
     redexes pos l (appl pos (valu None (lvabs None None v t)) t0)

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

(** produce t = true *)
let eq_true : popt -> tbox -> pbox =
  fun _loc t ->
    let true_ = cons None (Pos.none "true") (reco None A.empty) in
    let cond = equiv t true (valu None true_) in
    rest _loc (strict_prod None A.empty) cond

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
  | PSet(_,VoT_V,_) -> (V,e)
  | VPtr _          -> (V,e)

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
  | PSet(_,VoT_T,_) -> (T,e)
  | TPtr _          -> (T,e)
  | Repl(_,_)       -> (T,e)
  | Delm _          -> (T,e)

  | SWit _          -> (S,e)

  | Conv            -> (O,e)
  | Succ _          -> (O,e)
  | OWMu _          -> (O,e)
  | OWNu _          -> (O,e)
  | OSch _          -> (O,e)
  | ESch(s,_,_)     -> (s,e)

  | Vari(s,_)       -> (s,e)

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
  let f x = valu None (vari None x) in
  let id = (None, Pos.none "x", f) in
  unbox (case None (box v) (A.singleton c id))
