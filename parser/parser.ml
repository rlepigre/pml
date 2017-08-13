(** Main parsing module. This module defines an [Earley] parser for the
    language. *)


open Extra
open Pos
open Raw

(* Definition of the [locate] function used by [Earley]. *)
#define LOCATE locate

(* Parser of a list separated by a given string. *)
let lsep s elt =
  parser
  | EMPTY                    -> []
  | e:elt es:{_:STR(s) elt}* -> e::es

(* Parser of a (non-empty) list separated by a given string. *)
let lsep_ne s elt =
  parser
  | e:elt es:{_:STR(s) elt}* -> e::es

(* String litteral. *)
let str_lit =
  let normal = Earley.in_charset
    (List.fold_left Charset.del Charset.full ['\\'; '"'; '\r'])
  in
  let schar = parser
    | "\\\""   -> "\""
    | "\\\\"   -> "\\"
    | "\\n"    -> "\n"
    | "\\t"    -> "\t"
    | c:normal -> String.make 1 c
  in
  Earley.change_layout
    (parser "\"" cs:schar* "\"" -> String.concat "" cs)
    Earley.no_blank

(* Parser of a module path. *)
let parser path_atom = id:''[a-zA-Z0-9_]+''
let parser path = ps:{path_atom '.'}* f:path_atom -> ps @ [f]

(* Parser for the contents of a goal. *)
let parser goal_name = s:''\([^-]\|\(-[^}]\)\)*'' 
let parser goal = "{-" str:goal_name "-}" -> String.trim str

(* Identifiers. *)
let parser lid = id:''[a-z][a-zA-Z0-9_']*'' -> Keyword.check id; id
let parser uid = id:''[A-Z][a-zA-Z0-9_']*'' -> Keyword.check id; id

(* Located identifiers. *)
let parser llid = id:lid -> in_pos _loc_id id
let parser luid = id:uid -> in_pos _loc_id id

(* Lowercase identifier or wildcard (located). *)
let parser llid_wc =
  | id:lid -> in_pos _loc id
  | '_'    -> in_pos _loc "_"

(* Keywords. *)
let _sort_    = Keyword.create "sort"
let _include_ = Keyword.create "include"
let _type_    = Keyword.create "type"
let _def_     = Keyword.create "def"
let _val_     = Keyword.create "val"
let _fun_     = Keyword.create "fun"
let _save_    = Keyword.create "save"
let _restore_ = Keyword.create "restore"
let _case_    = Keyword.create "case"
let _of_      = Keyword.create "of"
let _fix_     = Keyword.create "fix"
let _rec_     = Keyword.create "rec"
let _corec_   = Keyword.create "corec"
let _let_     = Keyword.create "let"
let _in_      = Keyword.create "in"
let _if_      = Keyword.create "if"
let _else_    = Keyword.create "else"
let _true_    = Keyword.create "true"
let _false_   = Keyword.create "false"
let _bool_    = Keyword.create "bool"
let _show_    = Keyword.create "show"
let _use_     = Keyword.create "use"
let _qed_     = Keyword.create "qed"
let _using_   = Keyword.create "using"
let _deduce_  = Keyword.create "deduce"
let _print_   = Keyword.create "print"
let _check_   = Keyword.create "check"

(* Some useful tokens. *)
let parser elipsis = "⋯" | "..."
let parser arrow   = "→" | "->"
let parser impl    = "⇒" | "=>"
let parser scis    = "✂" | "8<"
let parser equiv   = "≡" | "="
let parser nequiv  = "≠"
let parser neg_sym = "¬"

(* Optional negation symbol. *)
let parser neg =
  | EMPTY   -> true
  | neg_sym -> false

(* Optional "rec" annotation of a term. *)
let parser v_is_rec =
  | EMPTY   -> false
  | _rec_   -> true

(* Optional "rec" / "corec" annotation for a type. *)
let parser t_is_rec =
  | EMPTY   -> `Non
  | _rec_   -> `Rec
  | _corec_ -> `CoRec

(* Optional elipsis for extensible records. *)
let parser is_strict =
  | EMPTY   -> true
  | elipsis -> false

(* Equivalence / inequivalence symbol. *)
let parser eq =
  | equiv   -> true
  | nequiv  -> false

(* Parser for sorts. *)
let parser sort (p : [`A | `F]) =
  | {"ι" | "<iota>"    | "<value>"  } when p = `A -> in_pos _loc SV
  | {"τ" | "<tau>"     | "<term>"   } when p = `A -> in_pos _loc ST
  | {"σ" | "<sigma>"   | "<stack>"  } when p = `A -> in_pos _loc SS
  | {"ο" | "<omicron>" | "<prop>"   } when p = `A -> in_pos _loc SP
  | {"κ" | "<kappa>"   | "<ordinal>"} when p = `A -> in_pos _loc SO
  | id:lid                            when p = `A -> in_pos _loc (SVar(id))
  | "(" s:(sort `F) ")"               when p = `A -> s
  | s1:(sort `A) arrow s2:(sort `F)   when p = `F -> in_pos _loc (SFun(s1,s2))
  | s:(sort `A)                       when p = `F -> s

(* Entry point for sorts. *)
let sort = sort `F

(* Priorities for parsing expressions. *)
type p_prio = [`A | `M | `R | `F] (* Atom, Memb, Rest, Full *)
type t_prio = [`A | `P | `S | `F] (* Atom, Appl, Sequ, Full *)

(* Parsing mode for expressions. *)
type mode = [`Any | `Prp of p_prio | `Trm of t_prio | `Stk | `Ord ]

(* Parser for expressions. *)
let parser expr (m : mode) =
  (* Any (higher-order function) *)
  | "(" x:llid s:{":" s:sort} "↦" e:(expr `Any)
      when m = `Any
      -> in_pos _loc (EHOFn(x,s,e))

  (* Proposition (variable and higher-order application) *)
  | id:llid args:{"<" (lsep "," (expr `Any)) ">"}?[[]]
      when m = `Prp`A
      -> in_pos _loc (EVari(id, args))
  (* Proposition (boolean type) *)
  | _bool_
      when m = `Prp`A
      -> p_bool (Some _loc)
  (* Proposition (implication) *)
  | a:(expr (`Prp`R)) impl b:(expr (`Prp`F))
      when m = `Prp`F
      -> in_pos _loc (EFunc(a,b))
  (* Proposition (non-empty product) *)
  | "{" fs:(lsep_ne ";" (parser l:llid ":" a:(expr (`Prp`F)))) s:is_strict "}"
      when m = `Prp`A
      -> in_pos _loc (EProd(fs,s))
  (* Proposition (extensible empty record) *)
  | "{" elipsis "}"
      when m = `Prp`A
      -> in_pos _loc (EProd([],false))
  (* Proposition / Term (empty product / empty record) *)
  | "{" "}"
      when m = `Prp`A || m = `Trm`A
      -> in_pos _loc EUnit
  (* Proposition (disjoint sum) *)
  | "[" fs:(lsep ";" (parser l:luid a:{_:_of_ a:(expr (`Prp`F))}?)) "]"
      when m = `Prp`A
      -> in_pos _loc (EDSum(fs))
  (* Proposition (universal quantification) *)
  | "∀" x:llid xs:llid* s:{':' s:sort}? ',' a:(expr (`Prp`F))
      when m = `Prp`F
      -> euniv _loc x xs s a
  (* Proposition (dependent function type) *)
  | "∀" x:llid xs:llid* "∈" a:(expr (`Prp`F)) ',' b:(expr (`Prp`F))
      when m = `Prp`F
      -> euniv_in _loc x xs a b
  (* Proposition (existential quantification) *)
  | "∃" x:llid xs:llid* s:{':' s:sort}? ',' a:(expr (`Prp`F))
      when m = `Prp`F
      -> eexis _loc x xs s a
  (* Proposition (set type) *)
  | "{" x:llid "∈" a:(expr (`Prp`F)) "}"
      when m = `Prp`A
      -> esett _loc x a
  (* Proposition (least fixpoint) *)
  | "μ" o:(expr `Ord)?[none EConv] x:llid a:(expr (`Prp`F))
      when m = `Prp`F
      -> in_pos _loc (EFixM(o,x,a))
  (* Proposition (greatest fixpoint) *)
  | "ν" o:(expr `Ord)?[none EConv] x:llid a:(expr (`Prp`F))
      when m = `Prp`F
      -> in_pos _loc (EFixN(o,x,a))
  (* Proposition (membership) *)
  | t:(expr (`Trm`P)) "∈" a:(expr (`Prp`M))
      when m = `Prp`M
      -> in_pos _loc (EMemb(t,a))
  (* Proposition (restriction) *)
  | a:(expr (`Prp`M)) "|" t:(expr (`Trm`P)) b:eq u:(expr (`Trm`P))
      when m = `Prp`R
      -> in_pos _loc (ERest(Some a,EEquiv(t,b,u)))
  (* Proposition (equivalence) *)
  | t:(expr (`Trm`P)) b:eq u:(expr (`Trm`P))
      when m = `Prp`A
      -> in_pos _loc (ERest(None,EEquiv(t,b,u)))
  (* Proposition (parentheses) *)
  | "(" (expr (`Prp`F)) ")"
      when m = `Prp`A
  (* Proposition (coersion) *)
  | (expr (`Prp`A)) when m = `Prp`M
  | (expr (`Prp`M)) when m = `Prp`R
  | (expr (`Prp`R)) when m = `Prp`F
  | (expr (`Prp`F)) when m = `Any

  (* Term (variable and higher-order application) *)
  | id:llid args:{"<" (lsep "," (expr `Any)) ">"}?[[]]
      when m = `Trm`A
      -> in_pos _loc (EVari(id, args))
  (* Term (lambda abstraction) *)
  | _fun_ args:arg+ arrow t:(expr (`Trm`F))
      when m = `Trm`F
      -> in_pos _loc (ELAbs((List.hd args, List.tl args),t))
  (* Term (constructor) *)
  | c:luid t:{"[" t:(expr (`Trm`F)) "]"}?$
      when m = `Trm`A
      -> in_pos _loc (ECons(c, Option.map (fun t -> (t, ref `T)) t))
  (* Term (true boolean) *)
  | _true_
      when m = `Trm`A
      -> v_bool _loc true
  (* Term (true boolean) *)
  | _false_
      when m = `Trm`A
      -> v_bool _loc false
  (* Term (record) *)
  | "{" fs:(lsep_ne ";" (parser l:llid "=" a:(expr (`Trm`F)))) "}"
      when m = `Trm`A
      -> in_pos _loc (EReco(List.map (fun (l,a) -> (l, a, ref `T)) fs))
  (* Term (scisors) *)
  | scis
      when m = `Trm`A
      -> in_pos _loc EScis
  (* Term (application) *)
  | t:(expr (`Trm`P)) u:(expr (`Trm`A))
      when m = `Trm`P
      -> in_pos _loc (EAppl(t,u))
  (* Term (let binding) *)
  | _let_ r:v_is_rec arg:let_arg '=' t:(expr (`Trm`F)) _in_ u:(expr (`Trm`F))
      when m = `Trm`F
      -> let_binding _loc r arg t u
  (* Term (sequencing). *)
  | t:(expr (`Trm`P)) ';' u:(expr (`Trm`S))
      when m = `Trm`S
      -> in_pos _loc (ESequ(t,u))
  (* Term (mu abstraction) *)
  | _save_ args:llid+ arrow t:(expr (`Trm`F))
      when m = `Trm`F
      -> in_pos _loc (EMAbs((List.hd args, List.tl args),t))
  (* Term (name) *)
  | _restore_ s:(expr `Stk) t:(expr (`Trm`F))
      when m = `Trm`F
      -> in_pos _loc (EName(s,t))
  (* Term (projection) *)
  | t:(expr (`Trm`A)) "." l:llid
      when m = `Trm`A
      -> in_pos _loc (EProj(t, ref `T, l))
  (* Term (case analysis) *)
  | _case_ t:(expr (`Trm`F)) '{' ps:{_:'|'? patt _:arrow (expr (`Trm`F))}* '}'
      when m = `Trm`A
      -> in_pos _loc (ECase(t, ref `T, ps))
  (* Term (conditional) *)
  | _if_ c:(expr (`Trm`F)) '{' t:(expr (`Trm`F)) '}'
      _else_ '{' e:(expr (`Trm`F)) '}'
      when m = `Trm`A
      -> if_then_else _loc c t e
  (* Term ("deduce" tactic) *)
  | _deduce_ a:(expr (`Prp`F))$
      when m = `Trm`A
      -> deduce _loc a
  (* Term ("show" tactic) *)
  | _show_ a:(expr (`Prp`F)) _using_ t:(expr (`Trm`P))$
      when m = `Trm`A
      -> show_using _loc a t
  (* Term ("use" tactic) *)
  | _use_ t:(expr (`Trm`P))$
      when m = `Trm`A
      -> use _loc t
  (* Term ("QED" tactic) *)
  | _qed_
      when m = `Trm`A
      -> qed _loc
  (* Term (fixpoint) *)
  | _fix_ t:(expr (`Trm`F))
      when m = `Trm`F
      -> in_pos _loc (EFixY(t))
  (* Term (printing) *)
  | _print_ s:str_lit
      when m = `Trm`A
      -> in_pos _loc (EPrnt(s))
  (* Term (type coersion) *)
  | "(" t:(expr (`Trm`F)) ":" a:(expr (`Prp`F)) ")"
      when m = `Trm`A
      -> in_pos _loc (ECoer(t,a))
  (* Term (parentheses) *)
  | "(" t:(expr (`Trm`F)) ")"
      when m = `Trm`A
  (* Term (level coersions) *)
  | (expr (`Trm`A)) when m = `Trm`P
  | (expr (`Trm`P)) when m = `Trm`S
  | (expr (`Trm`S)) when m = `Trm`F
  | (expr (`Trm`F)) when m = `Any

  (* Stack (variable and higher-order application) *)
  | id:llid args:{"<" (lsep "," (expr `Any)) ">"}?[[]]
      when m = `Stk
      -> in_pos _loc (EVari(id, args))
  (* Stack (empty) *)
  | "ε"
      when m = `Stk
      -> in_pos _loc EEpsi
  (* Stack (push) *)
  | v:(expr (`Trm`A)) "·" s:(expr `Stk)
      when m = `Stk
      -> in_pos _loc (EPush(v,s))
  (* Stack (frame) *)
  | "[" t:(expr (`Trm`F)) "]" s:(expr `Stk)
      when m = `Stk
      -> in_pos _loc (EFram(t,s))
  (* Stack (from anything) *)
  | (expr `Stk) when m = `Any

  (* Ordinal (variable and higher-order application) *)
  | id:llid args:{"<" (lsep "," (expr `Any)) ">"}?[[]]
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
  | (expr `Ord) when m = `Any

  (* Goal (term or stack) *)
  | s:goal
      when m = `Stk || m = `Trm`A
      -> in_pos _loc (EGoal(s))

(* Function argument. *)
and arg  =
  | id:llid_wc                               -> (id, None  )
  | "(" id:llid_wc ":" a:(expr (`Prp`F)) ")" -> (id, Some a)

(* Argument of let-binding. *)
and let_arg = id:llid_wc a:{':' a:(expr (`Prp`F))}?

(* Pattern. *)
and patt =
  | c:luid arg:{'[' id:llid_wc ao:{":" (expr (`Prp`F))}? ']'}?
  | _true_  -> (in_pos _loc "true" , None)
  | _false_ -> (in_pos _loc "false", None)

(* Common entry points. *)
let parser term = (expr (`Trm`F))
let parser prop = (expr (`Prp`F))
let parser any  = (expr `Any)

(* Auxiliary parser for sort arguments. *)
let parser sort_arg  = id:llid so:{":" s:sort}?
let parser sort_args = {'<' l:(lsep_ne "," sort_arg) '>'}?[[]]

(* Toplevel item. *)
let parser toplevel =
  (* Definition of a new sort. *)
  | _sort_ id:llid '=' s:sort
      -> fun () -> sort_def id s

  (* Definition of an expression. *)
  | _def_  id:llid args:sort_args s:{':' sort}? '=' e:any
      -> fun () -> expr_def id args s e

  (* Definition of a proposition (special case of expression). *)
  | _type_ r:t_is_rec id:llid args:sort_args '=' e:prop
      -> fun () -> type_def _loc r id args e

  (* Definition of a value (to be computed). *)
  | _val_ r:v_is_rec id:llid ':' a:prop '=' t:term
      -> fun () -> val_def r id a t

  (* Check of a subtyping relation. *)
  | _check_ r:neg a:prop "⊂" b:prop
      -> fun () -> check_sub a r b

  (* Inclusion of a file. *)
  | _include_ p:path
      -> fun () -> include_file p

(* Entry point of the parser. *)
let parser entry = toplevel*

(** Exception raised in case of parse error. *)
exception No_parse of pos * string option

(** Main parsing function taking as input a file name. *)
let parse_file : string -> toplevel list = fun fn ->
  let parse = Earley.parse_file entry Blank.blank in
  try List.map (fun act -> act ()) (parse fn)
  with Earley.Parse_error(buf, pos, msgs) ->
    let pos = Pos.locate buf pos buf pos in
    let msg = match msgs with [] -> None | x::_ -> Some x in
    raise (No_parse(pos, msg))
