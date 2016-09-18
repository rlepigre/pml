#define LOCATE locate

open Pos
open Blank
open Raw.Sort
open Raw.Expr

let lsep s elt =
  parser
  | EMPTY                      -> []
  | e:elt es:{_:STR(s) elt}* $ -> e::es

let parser lid = ''[a-z][a-zA-Z0-9_']*''
let parser uid = ''[A-Z][a-zA-Z0-9_']*''

let parser llid = id:lid -> in_pos _loc id
let parser luid = id:uid -> in_pos _loc id

let parser arrow = "→" | "->"
let parser impl  = "⇒" | "=>"
let parser equiv =
  | {"≡" | "="} -> true 
  | "≠"         -> false

(** Parser for sorts. *)
let parser sort (p : [`A | `F]) =
  | {"ι" | "<iota>"    | "<value>"  } when p = `A -> in_pos _loc V
  | {"τ" | "<tau>"     | "<term>"   } when p = `A -> in_pos _loc T
  | {"σ" | "<sigma>"   | "<stack>"  } when p = `A -> in_pos _loc S
  | {"ο" | "<omicron>" | "<prop>"   } when p = `A -> in_pos _loc P
  | {"κ" | "<kappa>"   | "<ordinal>"} when p = `A -> in_pos _loc O
  | id:lid                            when p = `A -> in_pos _loc (Var(id))
  | "(" s:(sort `F) ")"               when p = `A -> s
  | s1:(sort `A) arrow s2:(sort `F)   when p = `F -> in_pos _loc (Fun(s1,s2))
  | s:(sort `A)                       when p = `F -> s
let sort = sort `F

(** Parser for expressions *)
type p_prio = [`A | `F]
type t_prio = [`A | `Ap | `F]

type mode = [`Any | `Prp of p_prio | `Trm of t_prio | `Stk | `Ord ]

let parser expr (m : mode) =
  (* Proposition (variable and higher-order application) *)
  | id:llid args:{"(" (lsep "," (expr `Any)) "}"}?[[]]
      when m = `Prp`A
      -> in_pos _loc (EVari(id, args)) 
  (* Proposition (implication) *)
  | a:(expr (`Prp`A)) impl b:(expr (`Prp`F))
      when m = `Prp`F
      -> in_pos _loc (EFunc(a,b))
  (* Proposition (product) *)
  | "{" fs:(lsep ";" (parser l:llid ":" a:(expr (`Prp`F)))) "}"
      when m = `Prp`A
      -> in_pos _loc (EProd(fs))
  (* Proposition (disjoint sum) *)
  | "[" fs:(lsep ";" (parser l:llid "of" a:(expr (`Prp`F)))) "]"
      when m = `Prp`A
      -> in_pos _loc (EProd(fs))
  (* Proposition (universal quantification) *)
  | "∀" '(' x:llid ":" s:sort ")" a:(expr (`Prp`F))
      when m = `Prp`F
      -> in_pos _loc (EUniv(x,s,a))
  (* Proposition (existential quantification) *)
  | "∃" '(' x:llid ":" s:sort ")" a:(expr (`Prp`F))
      when m = `Prp`F
      -> in_pos _loc (EExis(x,s,a))
  (* Proposition (least fixpoint) *)
  | "μ" o:(expr `Ord)?[none EConv] x:llid a:(expr (`Prp`F))
      when m = `Prp`F
      -> in_pos _loc (EFixM(o,x,a))
  (* Proposition (greatest fixpoint) *)
  | "ν" o:(expr `Ord)?[none EConv] x:llid a:(expr (`Prp`F))
      when m = `Prp`F
      -> in_pos _loc (EFixN(o,x,a))
  (* Proposition (membership) *)
  | t:(expr (`Trm`A)) "∈" a:(expr (`Prp`A))
      when m = `Prp`A
      -> in_pos _loc (EMemb(t,a))
  (* Proposition (restriction) *)
  | a:(expr (`Prp`A)) "|" t:(expr (`Trm`A)) b:equiv u:(expr (`Trm`A))
      when m = `Prp`A
      -> in_pos _loc (ERest(Some a,(t,b,u)))
  (* Proposition (dot projection) *)
  | t:(expr (`Trm`A)) "." x:llid
      when m = `Prp`A
      -> in_pos _loc (EDPrj(t,x))
  (* Proposition (parentheses) *)
  | "(" (expr (`Prp`F)) ")"
      when m = `Prp`A
  (* Proposition (coersion) *)
  | (expr (`Prp`A))
      when m = `Prp`F
  (* Proposition (from anything) *)
  | (expr (`Prp`F))
      when m = `Any

  (* TODO *)
(*
  | LAbs : p ex loc option * (v ex, t ex) lbinder             -> v ex
  | Cons : M.key loc * v ex loc                               -> v ex
  | Reco : (pos option * v ex loc) M.t                        -> v ex
  | Scis :                                                       v ex
  | Valu : v ex loc                                           -> t ex
  | Appl : t ex loc * t ex loc                                -> t ex
  | MAbs : (s ex, t ex) lbinder                               -> t ex
  | Name : s ex loc * t ex loc                                -> t ex
  | Proj : v ex loc * M.key loc                               -> t ex
  | Case : v ex loc * (pos option * (v ex, t ex) lbinder) M.t -> t ex 
  | FixY : t ex loc * v ex loc                                -> t ex
  | VTyp : v ex loc * p ex loc                                -> v ex
  | TTyp : t ex loc * p ex loc                                -> t ex
  | VLam : ('a ex, v ex) lbinder                              -> v ex
  | TLam : ('a ex, t ex) lbinder                              -> t ex
*)
  (* Term (from anything) *)
  | (expr (`Trm`F))
      when m = `Any

  (* Stack (empty) *)
  | "ε"
      when m = `Stk
      -> in_pos _loc EEpsi
  (* Stack (push) *)
  | v:(expr (`Trm`F)) {"." | "·"} s:(expr `Stk)
      when m = `Stk
      -> in_pos _loc (EPush(v,s))
  (* Stack (frame) *)
  | "[" t:(expr (`Trm`F)) "]" s:(expr `Stk)
      when m = `Stk
      -> in_pos _loc (EFram(t,s))
  (* Stack (from anything) *)
  | (expr `Stk)
      when m = `Any

  (* Ordinal (variable and higher-order application) *)
  | id:llid args:{"(" (lsep "," (expr `Any)) "}"}?[[]]
      when m = `Ord
      -> in_pos _loc (EVari(id, args)) 
  (* Ordinal (infinite) *)
  | {"∞" | "<inf>"}
      when m = `Ord
      -> in_pos _loc EConv
  (* Ordinal (successor) *)
  | o:(expr `Ord) "+1"
      when m = `Ord
      -> in_pos _loc (ESucc(o))
  (* Ordinal (from anything) *)
  | (expr `Ord)
      when m = `Any
let expr = expr `Any

(** Toplevel. *)
let parser toplevel =
  | "sort" id:lid '=' s:sort
