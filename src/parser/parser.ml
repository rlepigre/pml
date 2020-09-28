(** Main parsing module. This module defines an [Earley] parser for the
    language. *)

open Earley_core
open Earley
open Extra
open Pos
open Output
open Bindlib
open Typing
open Raw
open Priority

(** Exception raised in case of parse error. *)
exception No_parse of pos

exception Check_failed of Ast.prop * bool * Ast.prop

let verbose   = ref true
let timed     = ref false
let recompile = ref false

let parsing_chrono = Chrono.create "parsing"

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
let no_dot =
  Earley.test ~name:"no_dot" Charset.full (fun buf pos ->
    let c,buf,pos = Input.read buf pos in
    if c <> '.' then ((), true) else ((), false))
let parser path = ps:{path_atom '.'}* f:path_atom no_dot -> ps @ [f]

(* Parser for the contents of a goal. *)
let parser goal_name = s:''\([^-]\|\(-[^}]\)\)*''
let parser goal = "{-" str:goal_name "-}" -> String.trim str

(* Keywords. *)
let _assert_  = Keyword.create "assert"
let _assume_  = Keyword.create "assume"
let _because_ = Keyword.create "because"
let _bool_    = Keyword.create "bool"
let _by_      = Keyword.create "by"
let _case_    = Keyword.create "case"
let _check_   = Keyword.create "check"
let _corec_   = Keyword.create "corec"
let _deduce_  = Keyword.create "deduce"
let _delim_   = Keyword.create "delim"
let _def_     = Keyword.create "def"
let _else_    = Keyword.create "else"
let _eqns_    = Keyword.create "eqns"
let _false_   = Keyword.create "false"
let _fix_     = Keyword.create "fix"
let _for_     = Keyword.create "for"
let _fun_     = Keyword.create "fun"
let _if_      = Keyword.create "if"
let _include_ = Keyword.create "include"
let _infix_   = Keyword.create "infix"
let _know_    = Keyword.create "know"
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

(* Infix *)
let reserved_infix = [ "≡"; "∈"; "=" ]

let parser infix_re = s:''[^][(){}a-zA-Z0-9_'"";,. \n\t\r]+'' ->
    if List.mem s reserved_infix then give_up (); s

let parser infix =
  s:infix_re ->
    begin
      try
        let open Env in
        let {name; prio=p; asso; hiho} = Hashtbl.find infix_tbl s in
        let epsilon = 1e-6 in
        let q = p -. epsilon in
        let (pl, pr) = match asso with
          | LeftAssoc  -> (p, q)
          | RightAssoc -> (q, p)
          | NonAssoc   -> (q, q)
        in
        let name = in_pos _loc_s name in
        let sym = evari (Some _loc_s) name in
        (sym, name, p, pl, pr, hiho)
      with Not_found -> give_up ()
    end
| (_,s,p,pl,pr,ho):infix - '_' - m:lid ->
    let m = evari (Some _loc_m) (in_pos _loc_m m) in
    let t = in_pos _loc (EProj(m,ref `T, s)) in
    (t, s, p, pl, pr,ho)

(* Located identifiers. *)
let parser llid = id:lid       -> in_pos _loc id
  | '(' (_,id,_,_,_,_):infix ')' -> id
let parser luid = id:uid       -> in_pos _loc id
                | _true_       -> in_pos _loc "true"
                | _false_      -> in_pos _loc "false"
let parser lnum = id:num       -> in_pos _loc id

(* Int. *)
let parser int  = s:''[0-9]+'' -> int_of_string s

(* Float. *)
let parser float = s:''[0-9]*\('.'[0-9]*\)?\([eE][-+]?[0-9]*\)?'' ->
  if s = "" then give_up (); float_of_string s

(* Lowercase identifier or wildcard (located). *)
let parser llid_wc =
  | id:lid -> in_pos _loc id
  | '_'    -> in_pos _loc "_"

(* Some useful tokens. *)
let parser elipsis = "⋯" | "..."
let parser infty   = "∞" | "<inf>"
let parser arrow   = "→"
let parser impl    = "⇒" -> Totality.Tot
                   | "→" -> Totality.Ter
                   | "↝" -> Totality.Any
let parser scis    = "✂"
let parser equiv   = "≡" | "=="
let parser nequiv  = "≠" | "!="
let parser neg_sym = "¬"
let parser prod    = "×"
let parser lambda  = "λ"
let parser langle  = "⟨"
let parser rangle  = "⟩"
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
  | {"ι"|"<iota>"   | "<value>"  }  when p <= As -> in_pos _loc sv
  | {"τ"|"<tau>"    | "<term>"   }  when p <= As -> in_pos _loc ST
  | {"σ"|"<sigma>"  | "<stack>"  }  when p <= As -> in_pos _loc SS
  | {"ο"|"<omicron>"| "<prop>"   }  when p <= As -> in_pos _loc SP
  | {"κ"|"<kappa>"  | "<ordinal>"}  when p <= As -> in_pos _loc SO
  | id:lid                          when p <= As -> in_pos _loc (SVar(id))
  | "(" s:(sort Fs) ")"             when p <= As -> s
  | s1:(sort As) arrow s2:(sort Fs) when p <= Fs -> in_pos _loc (SFun(s1,s2))

(* Entry point for sorts. *)
let sort = sort Fs

(* Auxiliary parser for sort arguments. *)
let parser s_arg  = id:llid so:{_:column s:sort}?
let parser s_lst  = l:(list1 s_arg comma)
let parser s_args = {_:langle l:s_lst _:rangle}?[[]]

let (<<=) = fun p1 p2 ->
  match p1, p2 with
  | _     , HO     -> true
  | Any   ,_       -> true
  | Prp p1, Prp p2 -> p1 <= p2
  | Trm p1, Trm p2 -> p1 <= p2
  | Stk   , Stk    -> true
  | Ord p1, Ord p2 -> p1 <= p2
  | _     , _      -> false

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
      -> (match e.elt  with EInfx(e,_) -> e | _ -> e)

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
  (* Proposition (implication) *)
  | a:(expr (Prp M)) _if_ t:(expr (Trm I)) bu:{eq (expr (Trm I))}?
      when m <<= Prp R
      -> let (b,u) = match bu with
           | Some(b,u) -> (b,u)
           | None      -> (true, Pos.none (ECons(Pos.none "true", None)))
         in in_pos _loc (EImpl(EEquiv(t,b,u), Some a))
  (* Proposition (parentheses) *)
  | "(" e:(expr (Prp F')) ")"
      when m <<= Prp A
      -> (match e.elt  with EInfx(e,_) -> e | _ -> e)
  (* Proposition (injection of term) *)
  | t:(expr (Trm I))
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
  (* Term ("int") *)
  | n:int
      when m <<= Trm A
      -> from_int _loc n
  (* Term (infix symbol) *)
  | t:(expr (Trm I)) (s,_,p,pl,pr,ho):infix when m <<= Trm I ->>
      let pl' = match t.elt with EInfx(_,p) -> p | _ -> 0.0 in
      let _ = if pl' > pl then give_up () in
      u:(expr (Trm I))
      -> let pr' = match u.elt with EInfx(_,p) -> p | _ -> 0.0 in
         if pr' > pr then give_up ();
         let t =
           if ho then
             let sort = none (SFun(_st, none (SFun(_st,_st)))) in
             in_pos _loc (EHOAp(s, sort, [t;u]))
           else
             in_pos _loc (EAppl(none (EAppl(s,t)), u)) in
         in_pos _loc (EInfx(t,p))
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
  | _check_ '{' u:term '}' _for_ '{' t:term '}'
    b:{_:_because_ '{' term '}' }?
      when m <<= Trm A
      -> in_pos _loc (ERepl(t,u,b))
  (* Term (totality by purity) *)
  | _delim_ '{' u:term '}'
      when m <<= Trm R
      -> in_pos _loc (EDelm(u))
  (* Term ("deduce" tactic) *)
  | _deduce_ a:prop $
      when m <<= Trm A
      -> deduce _loc a
  (* Term ("show" tactic) *)
  | _show_ a:prop _using_ t:{(expr (Trm R)) | '{' term '}'}
      when m <<= Trm R
      -> show_using _loc a t
  (* Term ("use" tactic) *)
  | _use_ t:(expr (Trm R))
      when m <<= Trm R
      -> use _loc t
  (* Term ("eqns" tactic) *)
  | _eqns_ a:term eqns:{ _:equiv b:(expr (Trm R))
                         p:{ _:_by_ p:(expr (Trm R))
                           | _:_using_ '{' p:term '}'}? -> (_loc,b,p) }*
      when m <<= Trm R
      -> equations _loc _loc_a a eqns
  (* Term ("showing" tactic) *)
  | _showing_   a:(expr (Prp R)) ';' p:(expr (Trm S))
      when m <<= Trm S
      -> showing _loc a p
  (* Term ("assume" tactic) *)
  | _assume_   a:(expr (Prp R)) ';' p:(expr (Trm S))
      when m <<= Trm S
      -> assume _loc a p
  (* Term ("know" tactic) *)
  | _know_   a:(expr (Prp R)) ';' p:(expr (Trm S))
      when m <<= Trm S
      -> know _loc a p
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
      -> (match t.elt  with EInfx(t,_) -> t | _ -> t)

  (* Ordinal (infinite) *)
  | infty
      when m <<= Ord E
      -> in_pos _loc EConv
  (* Ordinal (successor) *)
  | o:ordinal "+ₒ" n:int
      when m <<= Ord F
      -> in_pos _loc (ESucc(o,n))
  (* Ordinal (parenthesis) *)
  | "(" o:ordinal ")"
      when m <<= Ord E
      -> (match o.elt  with EInfx(o,_) -> o | _ -> o)

  (* Goal (term or stack) *)
  | s:goal
      when m <<= Stk || m <<= Trm A
      -> in_pos _loc (EGoal(s))

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
  | x:llid_wc "::" y:llid_wc      ->
      let fs = if y.elt <> "_" then [(Pos.none "tl", (y, None))] else [] in
      let fs = if x.elt <> "_" then (Pos.none "hd", (x, None))::fs else fs in
      (in_pos _loc "Cons", Some (`LetArgRec fs))
  | c:luid arg:{'[' let_arg ']'}? -> (c                  , arg )
  | "0"                           -> (in_pos _loc "Zero" , None)

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
  | _assert_ r:neg a:prop "⊂" b:prop
      -> fun () -> check_sub a r b

  (* Inclusion of a file. *)
  | _include_ p:path
      -> let fn = Env.find_module p in
         load_infix fn; fun () -> Include fn

  | _set_ l:set_param
      -> fun () -> Glbl_set l

  | _infix_ '(' s:infix_re ')' '=' name:lid
                                   hiho:{"⟨" "⟩"->true}?[false]
                                   "priority" prio:float
                                   asso:{ "left"  -> Env.LeftAssoc
                                        | "right" -> Env.RightAssoc
                                        | "non"   -> Env.NonAssoc }
                                   "associative"
      -> let infix = Env.{name;prio;asso;hiho} in
         Hashtbl.replace Env.infix_tbl s infix;
         fun () -> Infix(s,infix)

(* Entry point of the parser. *)
and parser entry = toplevel*

and interpret : bool -> Raw.toplevel -> unit =
  fun nodep top ->
  let verbose = !verbose && nodep in
  let open Env in
  match top with
  | Sort_def(id,s) ->
      let Ast.Sort s = unsugar_sort s in
      if verbose then
        out "sort %s ≔ %a\n%!" id.elt Print.sort s;
      add_sort id.elt s
  | Expr_def(id,s,e) ->
      let Box(s,e) = unsugar_expr e s in
      let ee = Bindlib.unbox e in
      if verbose then
        out "expr %s : %a ≔ %a\n%!" id.elt Print.sort s Print.ex ee;
      add_expr id s e
  | Valu_def(id,a,t) ->
      let a = unbox (to_prop (unsugar_expr a _sp)) in
      let t = unbox (to_term (unsugar_expr t _st)) in
      let (a, prf) = type_check t a in
      let v = Eval.eval (Erase.term_erasure t) in
      if verbose then
        out "val %s : %a\n%!" id.elt Print.ex a;
      (* out "  = %a\n%!" Print.ex (Erase.to_valu v); *)
      ignore prf;
      add_value id t a v
  | Chck_sub(a,n,b) ->
      let a = unbox (to_prop (unsugar_expr a _sp)) in
      let b = unbox (to_prop (unsugar_expr b _sp)) in
      if is_subtype a b <> n then raise (Check_failed(a,n,b));
      if verbose then
        begin
          let (l,r) = if n then ("","") else ("¬(",")") in
          out "showed %s%a ⊂ %a%s\n%!" l Print.ex a Print.ex b r;
        end;
  | Include(fn) ->
      if verbose then
        out "include %S\n%!" fn;
      Log.without (handle_file false) fn
  | Def_list(tops) ->
      List.iter (interpret nodep) tops
  | Glbl_set(l)    ->
      begin
        let open Ast in
        match l with
        | Alvl(b,d) -> Typing.default_auto_lvl := (b,d)
        | Logs s    -> Log.set_enabled s
      end;
  | Infix(sym,infix) ->
     add_infix sym infix

and load_infix fn =
  try  Env.load_infix fn
  with Env.Compile ->
    compile_file false fn;
    try Env.load_infix fn
    with Env.Compile -> failwith "source changed during compilation"

and compile_file : bool -> string -> unit = fun nodep fn ->
  if !verbose then out "[%s]\n%!" fn;
  Env.start fn;
  let save = !Env.env in
  Env.env := Env.empty;
  let ast = Chrono.add_time parsing_chrono parse_file fn in
  List.iter (interpret nodep) ast;
  Env.save_file fn;
  Env.env := save

(* Handling the files. *)
and handle_file nodep fn =
  try
    if !recompile && nodep then compile_file nodep fn;
    try Env.load_file fn
    with Env.Compile ->
      if nodep then
        begin
          compile_file nodep fn;
          try Env.load_file fn
          with Env.Compile ->
            failwith "source changed during compilation"
        end
      else (* allready compiled by load_infix if dep *)
        failwith "source changed during compilation"
  with
  | No_parse(p)             ->
      begin
        err_msg "No parse %a." Pos.print_short_pos p;
        Quote.quote_file stderr p;
        exit 1
      end
  | Unbound_sort(s, None  ) ->
      begin
        err_msg "Unbound sort %s." s;
        exit 1
      end
  | Unbound_sort(s, Some p) ->
      begin
        err_msg "Unbound sort %s (%a)." s Pos.print_short_pos p;
        Quote.quote_file stderr p;
        exit 1
      end
  | Sort_clash(t,s)         ->
      begin
        let _ =
          match t.pos with
          | None   -> err_msg "Sort %a expected for %a."
                        pretty_print_raw_sort s print_raw_expr t
          | Some p -> err_msg "Sort %a expected %a."
                        pretty_print_raw_sort s Pos.print_short_pos p;
                      Quote.quote_file stderr p
        in
        exit 1
      end
  | Too_many_args(e)        ->
      begin
        let _ =
          match e.pos with
          | None   -> err_msg "Expr %a has too many arguments."
                        print_raw_expr e
          | Some p -> err_msg "Expr %a has too many arguments."
                        print_raw_expr e;
                      Quote.quote_file stderr p
        in
        exit 1
      end
  | Unbound_variable(x,p)   ->
      begin
        let _ =
          match p with
          | None   -> err_msg "Unbound variable %s." x;
          | Some p -> err_msg "Unbound variable %s %a." x
                        Pos.print_short_pos p;
                      Quote.quote_file stderr p
        in
        exit 1
      end
  | Already_matched(c)      ->
      begin
        match c.pos with
        | None   -> err_msg "%s has already been matched." c.elt;
        | Some p -> err_msg "%s (%a) has already been matched." c.elt
                      Pos.print_short_pos p;
                    Quote.quote_file stderr p
      end;
      exit 1

(** Main parsing function taking as input a file name. *)
and parse_file : string -> toplevel list = fun fn ->
  let blank = Blanks.line_comments "//" in
  let parse = Earley.parse_file entry blank in
  try List.map (fun act -> act ()) (parse fn)
  with Parse_error(buf, pos) ->
    let pos = Pos.locate buf pos buf pos in
    raise (No_parse pos)
