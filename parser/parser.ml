(** Main parsing module. This module defines an [Earley] parser for the
    language. *)

open Earley
open Extra
open Pos
open Raw

(* Definition of the [locate] function used by [Earley]. *)
#define LOCATE locate

(* Reject if the given locatio is not on a single line. *)
let single_line _loc =
  if _loc.start_line <> _loc.end_line then give_up ()

(* String litteral. *)
let str_lit =
  let normal = List.fold_left Charset.del Charset.full ['\\'; '"'; '\r'] in
  let normal = in_charset normal in
  let str_char = parser
    | "\\\""   -> "\""
    | "\\\\"   -> "\\"
    | "\\n"    -> "\n"
    | "\\t"    -> "\t"
    | c:normal -> String.make 1 c
  in
  let str = parser "\"" cs:str_char* "\"" -> String.concat "" cs in
  change_layout str no_blank

(* Parser of a module path. *)
let parser path_atom = id:''[a-zA-Z0-9_]+''
let parser path = ps:{path_atom '.'}* f:path_atom -> ps @ [f]

(* Parser for the contents of a goal. *)
let parser goal_name = s:''\([^-]\|\(-[^}]\)\)*''
let parser goal = "{-" str:goal_name "-}" -> String.trim str

(* Keywords. *)
let _assume_  = Keyword.create "assume"
let _because_ = Keyword.create "because"
let _bool_    = Keyword.create "bool"
let _case_    = Keyword.create "case"
let _check_   = Keyword.create "check"
let _corec_   = Keyword.create "corec"
let _deduce_  = Keyword.create "deduce"
let _delim_   = Keyword.create "delim"
let _def_     = Keyword.create "def"
let _else_    = Keyword.create "else"
let _false_   = Keyword.create "false"
let _fix_     = Keyword.create "fix"
let _for_     = Keyword.create "for"
let _fun_     = Keyword.create "fun"
let _if_      = Keyword.create "if"
let _include_ = Keyword.create "include"
let _let_     = Keyword.create "let"
let _of_      = Keyword.create "of"
let _print_   = Keyword.create "print"
let _qed_     = Keyword.create "qed"
let _rec_     = Keyword.create "rec"
let _restore_ = Keyword.create "restore"
let _save_    = Keyword.create "save"
let _set_     = Keyword.create "set"
let _show_    = Keyword.create "show"
let _showing_ = Keyword.create "showing"
let _sort_    = Keyword.create "sort"
let _such_    = Keyword.create "such"
let _suppose_ = Keyword.create "suppose"
let _take_    = Keyword.create "take"
let _that_    = Keyword.create "that"
let _true_    = Keyword.create "true"
let _type_    = Keyword.create "type"
let _unsafe_  = Keyword.create "unsafe"
let _use_     = Keyword.create "use"
let _using_   = Keyword.create "using"
let _val_     = Keyword.create "val"

(* Identifiers. *)
let parser lid = id:''[a-z][a-zA-Z0-9_']*'' -> Keyword.check id; id
let parser uid = id:''[A-Z][a-zA-Z0-9_']*'' -> Keyword.check id; id
let parser num = id:''[0-9]+''              -> id

(* Located identifiers. *)
let parser llid = id:lid  -> in_pos _loc id
let parser luid = id:uid  -> in_pos _loc id
                | _true_  -> in_pos _loc "true"
                | _false_ -> in_pos _loc "false"
let parser lnum = id:num  -> in_pos _loc id

(* Int. *)
let parser int  = s:''[0-9]+'' -> int_of_string s

(* Lowercase identifier or wildcard (located). *)
let parser llid_wc =
  | id:lid -> in_pos _loc id
  | '_'    -> in_pos _loc "_"

(* Some useful tokens. *)
let parser elipsis = "⋯" | "..."
let parser infty   = "∞" | "<inf>"
let parser arrow   = "→" | "->"
let parser impl    = {"⇒" | "=>"} -> Totality.Tot
                   | {"→" | "->"} -> Totality.Ter
                   | {"↝" | "~>"} -> Totality.Any
let parser scis    = "✂" | "8<"
let parser equiv   = "≡" | "=="
let parser nequiv  = "≠"
let parser neg_sym = "¬"
let parser prod    = "×" | "*"
let parser lambda  = "λ"
let parser langle  = "<" | "⟨"
let parser rangle  = ">" | "⟩"
let parser empty_s = "[.]" | "∅"
let parser comma   = ","
let parser semi    = ";"
let parser column  = ":"

(* Such that. *)
let parser _st_ = _:_such_ _:_that_

(* Optional negation symbol. *)
let parser neg =
  | EMPTY   -> true
  | neg_sym -> false

(* Optional "rec" annotation on a value definition. *)
let parser v_rec =
  | EMPTY    -> `Non
  | _rec_    -> `Rec
  | _unsafe_ -> `Unsafe

(* Optional "rec" / "corec" annotation on a type definition. *)
let parser t_rec =
  | EMPTY   -> `Non
  | _rec_   -> `Rec
  | _corec_ -> `CoRec

(* Optional elipsis for extensible records. *)
let parser strict =
  | EMPTY       -> true
  | ';' elipsis -> false

(* Equivalence / inequivalence symbol. *)
let parser eq =
  | equiv   -> true
  | nequiv  -> false

type ps = Fs | As

(* Parser for sorts. *)
let parser sort @ (p : ps) =
  | {"ι" | "<iota>"    | "<value>"  } when p <= As -> in_pos _loc sv
  | {"τ" | "<tau>"     | "<term>"   } when p <= As -> in_pos _loc ST
  | {"σ" | "<sigma>"   | "<stack>"  } when p <= As -> in_pos _loc SS
  | {"ο" | "<omicron>" | "<prop>"   } when p <= As -> in_pos _loc SP
  | {"κ" | "<kappa>"   | "<ordinal>"} when p <= As -> in_pos _loc SO
  | id:lid                            when p <= As -> in_pos _loc (SVar(id))
  | "(" s:(sort Fs) ")"               when p <= As -> s
  | s1:(sort As) arrow s2:(sort Fs)   when p <= Fs -> in_pos _loc (SFun(s1,s2))

(* Entry point for sorts. *)
let sort = sort Fs

(* Auxiliary parser for sort arguments. *)
let parser s_arg  = id:llid so:{_:column s:sort}?
let parser s_lst  = l:(list1 s_arg comma)
let parser s_args = {_:langle l:s_lst _:rangle}?[[]]

(* Priorities for parsing propositions (Atom, Memb, Rest, Prod, Full). *)
type p_prio = F' | F | P | R | M | A

(* Priorities for parsing terms (Atom, aPpl, Infix, pRefix, Sequ, Full). *)
type t_prio = F | S | R | I | P | A

(* Priorities for parsing ordinel (Exponent, Full) *)
type o_prio = F | E

(* Parsing mode for expressions. *)
type mode = Any | Prp of p_prio | Trm of t_prio | Stk | Ord of o_prio | HO

let (<<=) = fun p1 p2 ->
  match p1, p2 with
  | _     , HO     -> true
  | Any   ,_       -> true
  | Prp p1, Prp p2 -> p1 <= p2
  | Trm p1, Trm p2 -> p1 <= p2
  | Stk   , Stk    -> true
  | Ord p1, Ord p2 -> p1 <= p2
  | _     , _      -> false

let to_full = function
(* Parser for expressions. *)
let parser expr @(m : mode) =
  (* Any (higher-order function) *)
  | "(" x:llid ":" s:sort "↦" e:any ")"
      when m <<= Any
      -> in_pos _loc (EHOFn(x,s,e))
  (* Higher-order application *)
  | e:(expr HO) args:ho_args
      when m <<= HO && m <> Ord E
      -> in_pos _loc (EHOAp(e, new_sort_uvar None, args))
  (* Variable *)
  | id:llid s:{'^' (expr (Ord E))}?
      when m <<= HO
      -> begin
           match s with
           | None   -> evari (Some _loc) id
           | Some s -> let id = Pos.make id.pos (id.elt ^ "#") in
                       let x = evari (Some _loc_id) id in
                       in_pos _loc (EHOAp(x, new_sort_uvar None, [s]))
         end
  (* Parenthesis niveau HO *)
  | '(' e:(expr Any) ')'
      when m = HO
      -> e

  (* Proposition (boolean type) *)
  | _bool_
      when m <<= Prp A
      -> p_bool (Some _loc)
  (* Proposition (implication) *)
  | a:(expr (Prp P)) t:impl b:prop
      when m <<= Prp F
      -> in_pos _loc (EFunc(t,a,b))
  (* Proposition (tuple type) *)
  | a:(expr (Prp R)) bs:{_:prod b:(expr (Prp R))}+
      when m <<= Prp P
      -> tuple_type _loc (a::bs)
  (* Proposition (non-empty product) *)
  | "{" fs:(list1 (parser l:llid ":" a:prop) semi) s:strict "}"
      when m <<= Prp A
      -> in_pos _loc (EProd(fs,s))
  (* Proposition (extensible empty record) *)
  | "{" elipsis "}"
      when m <<= Prp A
      -> in_pos _loc (EProd([],false))
  (* Proposition / Term (empty product / empty record) *)
  | "{" "}"
      when m <<= HO (* HO level to avoid ambiguity *)
      -> in_pos _loc EUnit
  (* Proposition (disjoint sum) *)
  | "[" fs:(list1 (parser l:luid a:{_:_of_ a:prop}?) semi) "]"
      when m <<= Prp A
      -> in_pos _loc (EDSum(fs))
  (* empty type *)
  | empty_s
      when m <<= Prp A
      -> in_pos _loc (EDSum [])
  (* Proposition (universal quantification) *)
  | "∀" x:llid xs:llid* s:{':' s:sort}? ',' a:prop
      when m <<= Prp F
      -> euniv _loc x xs s a
  (* Proposition (dependent function type) *)
  | "∀" x:llid xs:llid* "∈" a:prop ',' b:prop
      when m <<= Prp F
      -> euniv_in _loc x xs a b
  (* Proposition (existential quantification) *)
  | "∃" x:llid xs:llid* s:{':' s:sort}? ',' a:prop
      when m <<= Prp F
      -> eexis _loc x xs s a
  (* Proposition (dependent pair) *)
  | "∃" x:llid xs:llid* "∈" a:prop ',' b:prop
      when m <<= Prp F
      -> eexis_in _loc x xs a b
  (* Proposition (set type) *)
  | "{" x:llid "∈" a:prop "}"
      when m <<= Prp A
      -> esett _loc x a
  (* Proposition (least fixpoint) *)
  | "μ" o:{_:'_' ordinal}?[none EConv] x:llid ',' a:prop
      when m <<= Prp F
      -> in_pos _loc (EFixM(o,x,a))
  (* Proposition (greatest fixpoint) *)
  | "ν" o:{_:'_' ordinal}?[none EConv] x:llid ',' a:prop
      when m <<= Prp F
      -> in_pos _loc (EFixN(o,x,a))
  (* Proposition (membership) *)
  | t:(expr (Trm I)) "∈" a:(expr (Prp M))
      when m <<= Prp M
      -> in_pos _loc (EMemb(t,a))
  (* Proposition (restriction) *)
  | a:(expr (Prp M)) "|" t:(expr (Trm I)) bu:{eq (expr (Trm I))}?
      when m <<= Prp R
      -> let (b,u) = match bu with
           | Some(b,u) -> (b,u)
           | None      -> (true, Pos.none (ECons(Pos.none "true", None)))
         in in_pos _loc (ERest(Some a,EEquiv(t,b,u)))
  (* Proposition (equivalence) *)
  | t:(expr (Trm I)) b:eq u:(expr (Trm I))
      when m <<= Prp A
      -> in_pos _loc (ERest(None,EEquiv(t,b,u)))
  (* Proposition (parentheses) *)
  | "(" (expr (Prp F')) ")"
      when m <<= Prp A
  (* Proposition (injection of term) *)
  | t:(expr (Trm P))
      when m <<= Prp A && m <> Any && m <> Prp F'
      -> begin
          match t.elt with
            | EVari _ | EHOAp _ | EUnit -> give_up ()
            | _                         -> t
         end
  (* Term (lambda abstraction) *)
  | _fun_ args:arg+ '{' t:term '}'
      when m <<= Trm A
      -> in_pos _loc (ELAbs((List.hd args, List.tl args),t))
  | _take_ args:arg+ ';' t:(expr (Trm S))
      when m <<= Trm S
      -> in_pos _loc (ELAbs((List.hd args, List.tl args),t))
  | _suppose_ props:(list1 (expr (Prp F)) comma) ';' t:(expr (Trm S))
      when m <<= Trm S
      -> suppose _loc props t
  | lambda args:arg+ '.' t:(expr (Trm I))
      when m <<= Trm R
      -> single_line _loc;
         in_pos _loc (ELAbs((List.hd args, List.tl args),t))
  (* Term (constructor) *)
  | c:luid t:{"[" t:term "]"}?
      when m <<= Trm A
      -> in_pos _loc (ECons(c, Option.map (fun t -> (t, ref `T)) t))
  (* Term (empty list) *)
  | '[' ']'
      when m <<= Trm A
      -> v_nil _loc
  (* Term (list constructor) *)
  | t:(expr (Trm P)) "::" u:(expr (Trm I))
      when m <<= Trm I
      -> v_cons _loc t u
  (* Term (record) *)
  | "{" fs:(list1 field semi) "}"
      when m <<= Trm A
      -> record _loc fs
  (* Term (tuple) *)
  | "(" t:term "," ts:(list1 term comma) ")"
      when m <<= Trm A
      -> tuple_term _loc (t::ts)
  (* Term (scisors) *)
  | scis
      when m <<= Trm A
      -> in_pos _loc EScis
  (* Term (application) *)
  | t:(expr (Trm P)) u:(expr (Trm A))
      when m <<= Trm P
      -> in_pos _loc (EAppl(t,u))
  (* Term (let binding) *)
  | _let_ r:v_rec arg:let_arg '=' t:(expr (Trm R)) ';' u:(expr (Trm S))
      when m <<= Trm S
      -> let_binding _loc r arg t u
  (* Term (sequencing). *)
  | t:(expr (Trm R)) ';' u:(expr (Trm S))
      when m <<= Trm S
      -> in_pos _loc (ESequ(t,u))
  (* Term (mu abstraction) *)
  | _save_ arg:llid '{' t:term '}'
       when m <<= Trm A
      -> in_pos _loc (EMAbs(arg,t))
  (* Term (name) *)
  | _restore_ s:stack t:(expr (Trm A))
      when m <<= Trm I
      -> in_pos _loc (EName(s,t))
  (* Term (projection) *)
  | t:(expr (Trm A)) "." l:{llid | lnum}
      when m <<= Trm A
      -> in_pos _loc (EProj(t, ref `T, l))
  (* Term (case analysis) *)
  | _case_ t:term '{' ps:{_:'|'? patt _:arrow term}* '}'
      when m <<= Trm A
      -> pattern_matching _loc t ps
  (* Term (conditional) *)
  | _if_ c:term '{' t:term '}' e:{_:_else_ '{' term '}'}?
      when m <<= Trm A
      -> if_then_else _loc c t e
  (* Term (replacement) *)
  | _check_ u:term _for_ t:term _because_ p:(expr (Trm R))
      when m <<= Trm R
      -> in_pos _loc (ERepl(t,u,p))
  (* Term (totality by purity) *)
  | _delim_ '{' u:term '}'
      when m <<= Trm R
      -> in_pos _loc (EDelm(u))
  (* Term ("deduce" tactic) *)
  | _deduce_ a:prop$
      when m <<= Trm A
      -> deduce _loc a
  (* Term ("show" tactic) *)
  | _show_ a:prop _using_ t:(expr (Trm R))
      when m <<= Trm R
      -> show_using _loc a t
  (* Term ("use" tactic) *)
  | _use_ t:(expr (Trm R))
      when m <<= Trm R
      -> use _loc t
  (* Term ("showing" tactic) *)
  | _showing_   a:(expr (Prp R)) ';' p:(expr (Trm S))
      when m <<= Trm S
      -> showing _loc a p
  (* Term ("showing" tactic) *)
  | _assume_   a:(expr (Prp R)) ';' p:(expr (Trm S))
      when m <<= Trm S
      -> assume _loc a p
  (* Term ("QED" tactic) *)
  | _qed_
      when m <<= Trm A
      -> qed _loc
  (* Term (fixpoint) *)
  | _fix_ u:_unsafe_? arg:arg '{' t:term '}'
      when m <<= Trm F
      -> let (a,ao) = arg in
         let t = in_pos _loc (EFixY(u=None,a,t)) in
         let t = match ao with
           | None -> t
           | Some ty -> in_pos _loc (ECoer(new_sort_uvar None,t,ty))
         in
         t
  (* Term (printing) *)
  | _print_ s:str_lit
      when m <<= Trm A
      -> in_pos _loc (EPrnt(s))
  (* Term (type coersion) *)
  | "(" t:term ":" a:prop ")"
      when m <<= Trm A
      -> in_pos _loc (ECoer(new_sort_uvar None,t,a))
  (* Term (auto lvl) *)
  | _set_ l:set_param ';' t:(expr (Trm S))
      when m <<= Trm S
      -> in_pos _loc (EPSet(new_sort_uvar None,l,t))
  (* Term (let such that) *)
  | _let_ vs:s_lst _st_ x:llid_wc ':' a:prop ';' u:(expr (Trm S))
      when m <<= Trm S
      -> esuch _loc vs x a u
  (* Term (parentheses) *)
  | "(" t:term ")"
      when m <<= Trm A

  (* Ordinal (infinite) *)
  | infty
      when m <<= Ord E
      -> in_pos _loc EConv
  (* Ordinal (successor) *)
  | o:ordinal "+" n:int
      when m <<= Ord F
      -> in_pos _loc (ESucc(o,n))
  (* Ordinal (parenthesis) *)
  | "(" o:ordinal ")"
      when m <<= Ord E
      -> o

  (* Goal (term or stack) *)
  | s:goal
      when m <<= Stk || m <<= Trm A
      -> in_pos _loc (EGoal(s))

and in_par_expr (m:mode) = expr (to_full m)

(* Higher-order variable arguments. *)
and parser ho_args = {_:langle (list1 any comma) _:rangle}

(* Variable with optional type. *)
and parser arg_t = id:llid ao:{":" a:prop}?

(* Function argument. *)
and parser arg =
  | id:llid_wc                    -> (id, None  )
  | "(" id:llid_wc ":" a:prop ")" -> (id, Some a)

and parser field_nt =
  | a:arg_t            -> (fst a, a)
  | l:llid '=' a:arg_t -> (l    , a)

(* Argument of let-binding. *)
and parser let_arg =
  | id:llid_wc ao:{':' a:prop}?                -> `LetArgVar(id,ao)
  | '{' fs:(list1 field_nt semi) '}'           -> `LetArgRec(fs)
  | '(' f:arg_t ',' fs:(list1 arg_t comma) ')' -> `LetArgTup(f::fs)

(* Record field. *)
and parser field = l:llid {"=" t:(expr (Trm R))}?

(* Pattern. *)
and parser patt =
  | '[' ']'                       -> (in_pos _loc "Nil"  , None)
  | x:llid "::" y:llid            -> let hd = (Pos.none "hd", (x, None)) in
                                     let tl = (Pos.none "tl", (y, None)) in
                                     let arg = Some (`LetArgRec [hd; tl]) in
                                     (in_pos _loc "Cons" , arg )
  | c:luid arg:{'[' let_arg ']'}? -> (c                  , arg )

(* Common entry points. *)
and term    = expr (Trm F)
and prop    = expr (Prp F)
and stack   = expr Stk
and ordinal = expr (Ord F)
and any     = expr Any

(* Set general parameters *)
and parser set_param =
  | "auto" b:int d:int -> Ast.Alvl(b,d)
  | "log"  s:str_lit   -> Ast.Logs(s)

(* Toplevel item. *)
let parser toplevel =
  (* Definition of a new sort. *)
  | _sort_ id:llid '=' s:sort
      -> fun () -> sort_def id s

  (* Definition of an expression. *)
  | _def_  id:llid args:s_args s:{':' sort}? '=' e:any
      -> fun () -> expr_def id args s e

  (* Definition of a proposition (special case of expression). *)
  | _type_ r:t_rec id:llid args:s_args '=' e:prop
      -> fun () -> type_def _loc r id args e

  (* Definition of a value (to be computed). *)
  | _val_ r:v_rec id:llid ':' a:prop '=' t:term
      -> fun () -> val_def r id a t

  (* Check of a subtyping relation. *)
  | _check_ r:neg a:prop "⊂" b:prop
      -> fun () -> check_sub a r b

  (* Inclusion of a file. *)
  | _include_ p:path
      -> fun () -> include_file p

  | _set_ l:set_param
      -> fun () -> Glbl_set l

(* Entry point of the parser. *)
let parser entry = toplevel*

(** Exception raised in case of parse error. *)
exception No_parse of pos

(** Main parsing function taking as input a file name. *)
let parse_file : string -> toplevel list = fun fn ->
  let parse = parse_file entry Blank.blank in
  try List.map (fun act -> act ()) (parse fn)
  with Parse_error(buf, pos) ->
    let pos = Pos.locate buf pos buf pos in
    raise (No_parse pos)
