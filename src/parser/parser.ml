(** Main parsing module. This module defines an [Earley] parser for the
    language. *)

open Pos
open Pacomb
open Extra
open Output
open Bindlib
open Typing
open Raw
open Priority

exception Check_failed of Ast.prop * bool * Ast.prop

let verbose   = ref true
let timed     = ref false
let recompile = ref false

let parsing_chrono = Chrono.create "parsing"

(* String litteral. *)
let str_lit =
  let normal = List.fold_left Charset.del Charset.full ['\\'; '"'; '\r'] in
  let normal = Grammar.term (Lex.charset normal) in
  let%parser str_char =
      "\\\""      => "\""
    ; "\\\\"      => "\\"
    ; "\\n"       => "\n"
    ; "\\t"       => "\t"
    ; (c::normal) => String.make 1 c
  in
  let%parser [@layout Blank.none] str =
    "\"" (cs:: ~*str_char) "\"" => String.concat "" cs
  in
  str

(* Parser of a module path. *)

let%parser path_atom = (id::RE"[a-zA-Z0-9_]+") => id
let%parser path = (ps:: ~* ((p::path_atom) '.' => p)) (f::path_atom) => ps @ [f]

let path = Grammar.test_after (fun _ buf pos _ _ ->
               let (c,_,_) = Input.read buf pos in
               c <> '.') path

(* Parser for the contents of a goal. *)
let%parser goal_name = (s::RE"\\([^- \t\n\r]\\|\\(-[^}]\\)\\)+") => s
let%parser [@cache] goal =
  "{-" (str:: ~* goal_name) "-}" => String.trim (String.concat " " str)

module S = struct
  let id_charset = Charset.from_string "a-zA-2Z0-9_'"
  let reserved = []
end

module Keyword = Keywords.Make(S)

(* Keywords. *)
let _assert_  = Keyword.create "assert"
let _assume_  = Keyword.create "assume"
let _because_ = Keyword.create "because"
let _bool_    = Keyword.create "bool"
let _by_      = Keyword.create "by"
let _case_    = Keyword.create "case"
let _check_   = Keyword.create "check"
let _close_   = Keyword.create "close"
let _corec_   = Keyword.create "corec"
let _deduce_  = Keyword.create "deduce"
let _delim_   = Keyword.create "delim"
let _def_     = Keyword.create "def"
let _else_    = Keyword.create "else"
let _eqns_    = Keyword.create "eqns"
let _eval_    = Keyword.create "try_eval"
let _false_   = Keyword.create "false"
let _fix_     = Keyword.create "fix"
let _for_     = Keyword.create "for"
let _force_   = Keyword.create "force"
let _fun_     = Keyword.create "fun"
let _from_    = Keyword.create "from"
let _if_      = Keyword.create "if"
let _include_ = Keyword.create "include"
let _infix_   = Keyword.create "infix"
let _know_    = Keyword.create "know"
let _lazy_    = Keyword.create "lazy"
let _let_     = Keyword.create "let"
let _of_      = Keyword.create "of"
let _open_    = Keyword.create "open"
let _print_   = Keyword.create "print"
let _prove_   = Keyword.create "prove"
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
let _use_     = Keyword.create "use"
let _using_   = Keyword.create "using"
let _val_     = Keyword.create "val"

(* Identifiers. *)

let lid =
  Grammar.term (Lex.appl (fun id -> Keyword.check id; id)
      Regexp.(regexp (from_string "[a-z][a-zA-Z0-9_']*")))
let uid =
  Grammar.term (Lex.appl (fun id -> Keyword.check id; id)
      Regexp.(regexp (from_string "[A-Z][a-zA-Z0-9_']*")))
let%parser num = (id::RE"[0-9]+")              => id

let%parser because = _using_ => () ; _by_ => () ; _because_ => ()
let%parser deduce  = _show_  => () ; _deduce_ => () ; _prove_ => ()
let%parser from = _showing_ => () ; _from_ => ()

(* Infix *)
let reserved_infix = [ "≡"; "∈"; "="; "::" ]

let%parser minus =
  Grammar.test_after
    (fun _ buf pos _ _ ->
      let (c,_,_) = Input.read buf pos in
      not (c >= '0' && c <= '9'))
    ("-" => ())

let%parser infix_re = (s::RE"[^][(){}a-zA-Z0-9_'\";,. \n\t\r]+") =>
    (if s = "-" || List.mem s reserved_infix then Lex.give_up (); s)
  ; minus => "-"

let epsilon = 1e-6

let%parser rec infix =
  (s::infix_re) =>
    begin
      try
        let open Env in
        let {name; prio=p; asso; hiho} = Hashtbl.find infix_tbl s in
        let q = p -. epsilon in
        let (pl, pr) = match asso with
          | LeftAssoc  -> (p, q)
          | RightAssoc -> (q, p)
          | NonAssoc   -> (q, q)
        in
        let name = in_pos s_pos name in
        let sym = evari (Some s_pos) name in
        (pl,(sym, name,p,pr,hiho))
      with Not_found -> Lex.give_up ()
    end
; ((pl,(__,s,p,pr,ho))::infix) '_' (m::lid) =>
    begin
      let m = evari (Some m_pos) (in_pos m_pos m) in
      let t = in_pos _pos (EProj(m,ref `T, s)) in
      (pl,(t, s,p,pr,ho))
    end

let%parser [@layout Blank.none] infix = (i::infix) => i

(* Located identifiers. *)
let%parser llid = (id::lid)                => in_pos _pos id
  ; '(' ((__,(__,id,__,__,__))::infix) ')' => id
let%parser luid = (id::uid)    => in_pos _pos id
                ; _true_       => in_pos _pos "true"
                ; _false_      => in_pos _pos "false"
let%parser lnum = (id::num)    => in_pos _pos id

(* Int. *)
let%parser int  = (s::INT) => s

(* Bool. *)
let%parser bool = "true" => true ; "false" => false

(* Float. *)
let%parser float = (s::FLOAT) => s

(* Lowercase identifier or wildcard (located). *)
let%parser llid_wc =
    (id::llid) => id
  ; '_'        => in_pos _pos "_"

(* Some useful tokens. *)
let%parser elipsis = "⋯" => () ; "..." => ()
let%parser [@cache] infty   = "∞" => () ; "<inf>" => ()
let%parser arrow   = "→" => ()
let%parser impl    = "⇒" => Effect.bot
                   ; "→" => Effect.(known [CallCC])
                   ; "⇏" => Effect.(known [Loop])
                   ; "↛" => Effect.top
let%parser scis    = "✂" => ()
let%parser equiv   = "≡" => () ; "==" => ()
let%parser nequiv  = "≠" => () ; "!=" => ()
let%parser neg_sym = "¬" => ()
let%parser prod    = "×" => ()
let%parser lambda  = "λ" => ()
let%parser langle  = "⟨" => ()
let%parser rangle  = "⟩" => ()
let%parser empty_s = "[.]" => () ; "∅" => ()
let%parser comma   = "," => ()
let%parser semi    = ";" => ()
let%parser column  = ":" => ()
let%parser simpl   = "↪" => ()
let%parser memb    = "∈" => ()
let%parser rest    = "|" => ()
let%parser cvg     = "↓" => ()

(* Such that. *)
let%parser _st_ = _such_ _that_ => ()

(* Optional negation symbol. *)
let%parser neg =
    ()      => true
  ; neg_sym => false

(* Optional "rec" annotation on a value definition. *)
let%parser v_rec =
    ()       => `Non
  ; _rec_    => `Rec

(* Optional "rec" / "corec" annotation on a type definition. *)
let%parser t_rec =
    ()      => `Non
  ; _rec_   => `Rec
  ; _corec_ => `CoRec

(* Optional elipsis for extensible records. *)
let%parser strict =
    ()          => true
  ; ';' elipsis => false

(* Equivalence / inequivalence symbol. *)
let%parser eq =
    equiv   => true
  ; nequiv  => false

type ps = Fs | As

(* Parser for sorts. *)
let%parser rec sort (p : ps) =
    ("ι" => () ; "<iota>"    => () ; "<value>"   => ()) => in_pos _pos sv
  ; ("τ" => () ; "<tau>"     => () ; "<term>"    => ()) => in_pos _pos ST
  ; ("σ" => () ; "<sigma>"   => () ; "<stack>"   => ()) => in_pos _pos SS
  ; ("ο" => () ; "<omicron>" => () ; "<prop>"    => ()) => in_pos _pos SP
  ; ("κ" => () ; "<kappa>"   => () ; "<ordinal>" => ()) => in_pos _pos SO
  ; (id::lid)                                    => in_pos _pos (SVar(id))
  ; "(" (s::sort Fs) ")"                         => s
  ; (p<=Fs) (s1::sort As) arrow (s2::sort Fs)    => in_pos _pos (SFun(s1,s2))

(* Entry point for sorts. *)
let sort = sort Fs

(* Auxiliary parser for sort arguments. *)
let%parser s_arg  = (id::llid) (so:: ~? (column (s::sort) => s))  => (id,so)
let%parser s_lst  = (l:: ~+ [comma] s_arg)                        => l
let%parser s_args = (l:: ~? [[]] (langle (l::s_lst) rangle => l)) => l

let get_infix_prio u =
  match u.elt with EInfx(_,p) -> p
                 | _ -> 0.0

(*let to_full = function*)
(* Parser for expressions. *)
let%parser rec expr (m : mode) =
  (* Any (higher-order function) *)
    (e::ho_fun)                          => e
  (* Higher-order application *)
  ; (m <> Ord E) (e::ho_app)             => e
  (* Variable *)
  ; (e::expr_var)                        => e
  (* Parenthesis *)
  ; (e::expr_par (reset m))              => e

  ; (m <<= Prp A) (e::prop_atom)  => e
  ; (m <<= Prp A) (e::cond false (m = Any))
                                         => in_pos _pos (ERest(None,e))

  ; (m <<= Prp F) (e::prop_full)         => e
  ; (m <<= Prp P) (e::prop_prod)         => e
  ; (m <<= Prp M) (e::prop_mem)          => e
  ; (m <<= Prp R) (e::prop_rest)         => e
  (* Proposition / Term (empty product / empty record) *)
  ; (m <<= HO) "{" "}" (* HO level to avoid ambiguity *)
      => in_pos _pos EUnit

  ; (m <<= Trm I) (t::term_infix)        => t
  ; (m <<= Trm A) (t::term_atom)         => t
  ; (m <<= Trm S) (t::term_seq)          => t
  ; (m <<= Trm R) (t::term_repl)         => t
  ; (m <<= Trm P) (t::term_appl)         => t

  (* Ordinal (infinite) *)
  ; (m <<= Ord E) infty                  => in_pos _pos EConv
  ; (m <<= Ord F) (o::ord_full)          => o

  (* Goal (term or stack) *)
  ; (m <<= Stk || m <<= Trm A) (s::goal) => in_pos _pos (EGoal(s))

and [@cache] ho_fun =
  "(" (x::llid) ":" (s::sort) "↦" (e::any) ")"
      => in_pos _pos (EHOFn(x,s,e))

and [@cache] ho_app =
    (e::expr HO) (args::ho_args)
      => in_pos _pos (EHOAp(e, new_sort_uvar None, args))
  ; "ψ"
    => in_pos _pos ECPsi

and [@cache] expr_var =
    (id::llid) (s:: ~? ('^' (e::expr (Ord E)) => e))
      => begin
           match s with
           | None   -> evari (Some _pos) id
           | Some s -> let id = in_pos id.pos (id.elt ^ "#") in
                       let x = evari (Some id_pos) id in
                       in_pos _pos (EHOAp(x, new_sort_uvar None, [s]))
         end

and [@cache] expr_par m =
    '(' (e::(expr (reset m))) ')'
      => (match e.elt  with EInfx(e,_) -> e | _ -> e)

and [@cache] prop_atom =
  (* Proposition (boolean type) *)
    _bool_
      => p_bool (Some _pos)
  (* Proposition (non-empty product) *)
  ; "{" (fs::~+ [semi] ((l::llid) ":" (a::prop) => (l,a))) (s::strict) "}"
      => in_pos _pos (EProd(fs,s))
  (* Proposition (extensible empty record) *)
  ; "{" elipsis "}"
      => in_pos _pos (EProd([],false))
  (* Proposition (disjoint sum) *)
  ; "[" (fs::~+ [semi] ((l::luid) (a::~? (_of_ (a::prop) => a)) => (l,a))) "]"
      => in_pos _pos (EDSum(fs))
  (* empty type *)
  ; empty_s
      => in_pos _pos (EDSum [])
  (* Proposition (set type) *)
  ; "{" (x::llid) "∈" (a::prop) "}"
      => esett _pos x a

and [@cache] ord_full =
  (* Ordinal (successor) *)
    (o::ordinal) "+ₒ" (n::int)
      => in_pos _pos (ESucc(o,n))

and [@cache] prop_prod =
  (* Proposition (tuple type) *)
    (a::expr (Prp R)) (bs:: ~+ (prod (b::expr (Prp R)) => b))
      => tuple_type _pos (a::bs)

and [@cache] prop_mem =
  (* Proposition (membership) *)
    (t::expr (Trm I)) memb (a::expr (Prp M))
      => in_pos _pos (EMemb(t,a))

and [@cache] prop_rest =
  (* Proposition (restriction) *)
    (a::expr (Prp M)) rest (e::cond true false)
      => in_pos _pos (ERest(Some a,e))
  (* Proposition (implication) *)
  ; (e::cond true false) simpl (a::expr (Prp M))
      => in_pos _pos (EImpl(e, Some a))

and [@cache] prop_full =
  (* Proposition (implication) *)
    (a::expr (Prp P)) (t::impl) (b::prop)
      => in_pos _pos (EFunc(t,a,b,NoLz))
  ; _lazy_ langle (b::prop) rangle
      => (let t = Effect.create ~absent:[CallCC] () in
          in_pos _pos (EFunc(t,in_pos _pos (EProd([],true)), b, Lazy)))
  (* Proposition (universal quantification) *)
  ; "∀" (x::llid) (xs::~* llid) (s::~? (':' (s::sort) => s)) ',' (a::prop)
      => euniv _pos x xs s a
  (* Proposition (dependent function type) *)
  ; "∀" (x::llid) (xs::~* llid) "∈" (a::prop) ',' (b::prop)
      => euniv_in _pos x xs a b
  (* Proposition (existential quantification) *)
  ; "∃" (x::llid) (xs::~* llid) (s::~? (':' (s::sort) => s)) ',' (a::prop)
      => eexis _pos x xs s a
  (* Proposition (dependent pair) *)
  ; "∃" (x::llid) (xs::~* llid) "∈" (a::prop) ',' (b::prop)
      => eexis_in _pos x xs a b
  (* Proposition (least fixpoint) *)
  ; "μ" (o:: ~? [none EConv] ('_' (o::ordinal) => o)) ((x,s)::s_arg) ',' (a::any)
      => (let s = match s with Some s -> s | None -> new_sort_uvar (Some x) in
         in_pos _pos (EFixM(s,o,x,a)))
  (* Proposition (greatest fixpoint) *)
  ; "ν" (o:: ~? [none EConv] ('_' (o::ordinal) => o)) ((x,s)::s_arg) ',' (a::any)
      => (let s = match s with Some s -> s | None -> new_sort_uvar (Some x) in
         in_pos _pos (EFixN(s,o,x,a)))

and [@cache] term_atom  =
    (* Term (lambda abstraction) *)
    _fun_ (args::~+ arg) '{' (t::term) '}'
      => in_pos _pos (ELAbs((List.hd args, List.tl args),t,NoLz))
  ; _lazy_ '{' (t::term) '}'
      => (let unit = Some(in_pos _pos (EProd([],true))) in
          in_pos _pos (ELAbs(((in_pos _pos "_", unit), []),t,Lazy)))
  (* Term (printing) *)
  ; _print_ (s::str_lit)
      => in_pos _pos (EPrnt(s))
  (* Term (type coersion) *)
  ; "(" (t::term) ":" (a::prop) ")"
      => in_pos _pos (ECoer(new_sort_uvar None,t,a))
  (* Term (constructor) *)
  ; (c::luid) (t::~? ('[' (t::term) ']' => t))
      => in_pos _pos (ECons(c, Option.map (fun t -> (t, ref `T)) t))
  (* Term (empty list) *)
  ; '[' ']'
      => v_nil _pos
  (* Term ("int") *)
  ; (n::int)
      => from_int _pos n
  (* Term (record) *)
  ; "{" (fs::~+ [semi] field) "}"
      => record _pos fs
  (* Term (tuple) *)
  ; '(' (t::term) "," (ts::~+ [comma] term) ')'
      => tuple_term _pos (t::ts)
  (* Term (scisors) *)
  ; scis
      => in_pos _pos EScis
  ; "χ"
    => in_pos _pos (ELAbs (((in_pos _pos "x",None), []),
                           in_pos _pos (EClck(in_pos _pos (EVari(none "x",_sv)))), NoLz))
  (* Term (mu abstraction) *)
  ; _save_ (arg::llid) '{' (t::term) '}'
      => in_pos _pos (EMAbs(arg,t))
  (* Term (projection) *)
  ; (t::expr (Trm A)) "." (l::((l::llid) => l ; (l::lnum) => l))
      => in_pos _pos (EProj(t, ref `T, l))
  (* Term (case analysis) *)
  ; _case_ (t::term) '{'
      (ps::~* ((~? '|') (p::patt) arrow (t::term) => (p,t)))
      '}'
      => pattern_matching _pos t ps
  (* Term (conditional) *)
  ; _if_ (c::term) '{' (t::term) '}' (e::~? (_else_ '{' (t::term) '}' => t))
      => if_then_else _pos c t e
  (* Term ("QED" tactic) *)
  ; _qed_
      => qed _pos
  (* Term (fixpoint) *)
  ; _fix_ (arg::arg) '{' (t::term) '}'
      => (let (a,ao) = arg in
         let t = in_pos _pos (EFixY(a,t)) in
         let t = match ao with
           | None -> t
           | Some ty -> in_pos _pos (ECoer(new_sort_uvar None,t,ty))
         in
         t)

and [@cache] term_appl =
  (* Term (application) *)
    (t::expr (Trm P)) (u::expr (Trm A))
      => in_pos _pos (EAppl(t,u,NoLz))
  ; _force_ (t::expr (Trm A))
      => in_pos _pos (EAppl(t,in_pos _pos (EReco []),Lazy))

and [@cache] term_repl =
  (* Term (replacement) *)
    _check_ (u::((e::expr (Trm R)) => e ; '{' (t::term) '}' => t))
      _for_ (t::((e::expr (Trm R)) => e ; '{' (t::term) '}' => t))
            (b::~? justification)
      => in_pos _pos (ERepl(t,u,b))
  (* Term (totality by purity) *)
  ; _delim_ '{' (u::term) '}'
      => in_pos _pos (EDelm(u))
  (* Term ("show" tactic) *)
  ; deduce (a::prop) (p::~? justification)
      => show _pos a p
  (* Term ("show" tactic, sequences of eqns) *)
  ; deduce (a::term) (eqns::~+( equiv
                           (b::expr (Trm R))
                           (p::~? justification)
                              => (_pos,b,p)))
      => (if List.length eqns <= 1 then Lex.give_up ();
         equations _pos a_pos a eqns)
  (* Term ("use" tactic) *)
  ; _use_ (t::expr (Trm R))
    => use _pos t
  ; _eval_ (t::expr (Trm R))
      => eval _pos t
  ; lambda (args::~+ arg) '.' (t::expr (Trm I))
      => in_pos _pos (ELAbs((List.hd args, List.tl args),t,NoLz))



and [@cache] term_seq =
    _take_ (args::~+ arg) ';' (t::expr (Trm S))
      => in_pos _pos (ELAbs((List.hd args, List.tl args),t,NoLz))
  ; _suppose_ (props::~+ [comma] (expr (Prp F))) ';' (t::expr (Trm S))
      => suppose _pos props t
  (* Term (let binding) *)
  ; _let_ (r::v_rec) (arg::let_arg) '=' (t::expr (Trm R)) ';' (u::expr (Trm S))
      => let_binding _pos r arg t u
  (* Local definition *)
  ; _def_ (id::llid) (args::s_args) (s::~?(':' (s::sort) => s)) '=' (e::any)
          ';' (u::expr (Trm S))
      => local_expr_def _pos id args s e u
  (* local definition of a proposition (special case of expression). *)
  ; _type_ (r::t_rec) (id::llid) (args::s_args) '=' (e::prop) ';' (u::expr (Trm S))
      => local_type_def _pos r id args e u
  (* Term (sequencing). *)
  ; (t::expr (Trm R)) ';' (u::expr (Trm S))
      => in_pos _pos (ESequ(t,u))
  (* Term ("showing" tactic) *)
  ; from (a::expr (Prp R))
         (q::~? (because (q::((e::expr (Trm R)) => e ; '{' (t::term) '}' => t)) => q))
         ';' (p::expr (Trm S))
      => showing _pos a q p
  (* Term ("assume"/"know" tactic) *)
  ; (ass::(_assume_ => true; _know_ => false)) (a::expr (Trm R))
         (q::~? (because (q::((e::expr (Trm R)) => e ; '{' (t::term) '}' => t)) => q))
         ';' (p::expr (Trm S))
      => assume _pos ass a q p
  (* Term (auto lvl) *)
  ; _set_ (l::set_param) ';' (t::expr (Trm S))
      => in_pos _pos (EHint(LSet(l),t))
  (* Term (let such that) *)
  ; _let_ (vs::s_lst) _st_ (x::llid_wc) ':' (a::prop) ';' (u::expr (Trm S))
      => esuch _pos vs x a u
  ; _close_ (lids :: ~+ llid) ';' (u::expr (Trm S))
      => ehint _pos (Close(true,lids)) u
  ; _open_  (lids :: ~+ llid) ';' (u::expr (Trm S))
      => ehint _pos (Close(false,lids)) u

and [@cache] term_iprio =
  (t::expr (Trm I)) => (get_infix_prio t,t)

and [@cache] term_infix =
  (* Term (name) *)
    _restore_ (s::stack) (t::expr (Trm P))
      => in_pos _pos (EName(s,t))
  (* Term (infix symbol) *)
  ; ((pl',t)>:term_iprio)
      (s::(s::"::" => (let p = 5.0 in if pl' > p -. epsilon then Lex.give_up ();s)))
      ((pr',u)::term_iprio)
    => (let p = 5.0 in
        if pr' > p then Lex.give_up ();
        let t =
          in_pos _pos (ECons(in_pos s_pos "Cons",
            Some (record _pos [(none "hd", Some t)
                              ; (none "tl", Some u)], ref `T)))
        in
        in_pos _pos (EInfx(t,p)))
  ; ((pl',t)>:term_iprio)
      ((s,__,p,pr,ho)::((pl,i)::infix => (if pl' > pl then Lex.give_up (); i)))
      ((pr',u)::term_iprio)
    => (if pr' > pr then Lex.give_up ();
        let t =
          if ho then
            let sort = none (SFun(_st, none (SFun(_st,_st)))) in
            in_pos _pos (EHOAp(s, sort, [t;u]))
          else
            in_pos _pos (EAppl(none (EAppl(s,t,NoLz)), u,NoLz)) in
        in_pos _pos (EInfx(t,p)))

and justification =
  because (p::((t::expr (Trm R)) => t ; '{' (t::term)  '}' => t)) => p

and [@cache] cond opt any =
    (opt = true) (t::expr (Trm I))
            => (let u = none (ECons(none "true", None))
               in EEquiv(t,true,u))
  ; (opt = false && any = false) (t::expr (Trm I)) =>
      begin
         match t.elt with
            | EVari _ | EHOAp _ | EUnit -> Lex.give_up ()
            | _                         ->
               let u = none (ECons(none "true", None)) in
               EEquiv(t,true,u)
      end

  ; (t::expr (Trm I)) (b::eq) (u::expr (Trm I))
            => EEquiv(t,b,u)
  ; (t::expr (Trm I)) cvg
            => ENoBox(t)

(* Higher-order variable arguments. *)

and ho_args = langle (l:: ~+ [comma] any) rangle => l

(* Variable with optional type. *)
and arg_t = (id::llid) (ao::~? (":" (a::prop) => a)) => (id,ao)

(* Function argument. *)
and arg =
    (id::llid_wc)                       => (id, None  )
  ; "(" (id::llid_wc) ":" (a::prop) ")" => (id, Some a)

and field_nt =
    (a::arg_t)               => (fst a, a)
  ; (l::llid) '=' (a::arg_t) => (l    , a)

(* Argument of let-binding. *)
and let_arg =
    (id::llid_wc) (ao::~? (':' (a::prop) => a))   => `LetArgVar(id,ao)
  ; '{' (fs::~+ [semi] field_nt) '}'              => `LetArgRec(fs)
  ; '(' (f::arg_t) ',' (fs::~+ [comma] arg_t) ')' => `LetArgTup(f::fs)

(* Record field. *)
and field = (l::llid) (t::~? ("=" (t::expr (Trm R)) => t)) => (l,t)

(* Pattern. *)
and patt =
    '[' ']'                        => (in_pos _pos "Nil"  , None)
  ; (x::llid_wc) "::" (y::llid_wc) => (
      let fs = if y.elt <> "_" then [(none "tl", (y, None))] else [] in
      let fs = if x.elt <> "_" then (none "hd", (x, None))::fs else fs in
      (in_pos _pos "Cons", Some (`LetArgRec fs)))
  ; (c::luid) (arg::~?('[' (a::let_arg) ']' => a))
                                   => (c                  , arg )
  ; "0"                            => (in_pos _pos "Zero" , None)

(* Common entry points. *)
and term    = expr (Trm F)
and prop    = expr (Prp F)
and stack   = expr Stk
and ordinal = expr (Ord F)
and any     = expr Any

(* Set general parameters *)
and set_param =
    "auto" (b::int) (d::int) => Ast.Alvl(b,d)
  ; "log"  (s::str_lit)      => Ast.Logs(s)
  ; "keep_intermediate"
           (b::bool)         => Ast.Keep(b)

let%parser oc = () => None ; _close_ => Some true; _open_ => Some false

(* Toplevel item. *)
let%parser rec toplevel =
  (* Definition of a new sort. *)
    _sort_ (id::llid) '=' (s::sort)
      => (fun () -> sort_def id s)

  (* Definition of an expression. *)
  ; _def_  (id::llid) (args::s_args) (s::~?(':' (s::sort) => s)) '=' (e::any)
      => (fun () -> expr_def id args s e)

  (* Definition of a proposition (special case of expression). *)
  ; _type_ (r::t_rec) (id::llid) (args::s_args) '=' (e::prop)
      => (fun () -> type_def _pos r id args e)

  (* Definition of a value (to be computed). *)
  ; _val_ (r::v_rec) (oc::oc) (id::llid) ':' (a::prop) '=' (t::term)
      => (fun () -> val_def r id oc a t)

  (* Check of a subtyping relation. *)
  ; _assert_ (r::neg) (a::prop) "⊂" (b::prop)
      => (fun () -> check_sub a r b)

  (* Inclusion of a file. *)
  ; _include_ (p::path)
      => (let fn = Env.find_module p in
         load_infix fn; fun () -> Include fn)

  ; _set_ (l::set_param)
      => (fun () -> Glbl_set l)

  ; _infix_ '(' (s::infix_re) ')' '=' (name::lid)
      (hiho::~? [false] ("⟨" "⟩"=>true))
      "priority" (prio::float)
      (asso::( "left"  => Env.LeftAssoc
             ; "right" => Env.RightAssoc
             ; "non"   => Env.NonAssoc ))
               "associative"
    => (let infix = Env.{name;prio;asso;hiho} in
        Hashtbl.replace Env.infix_tbl s infix;
        fun () -> Infix(s,infix))

  ; _close_ (lids :: ~+ llid)
    => (fun () -> clos_def true lids)

  ; _open_ (lids :: ~+ llid)
    => (fun () -> clos_def false lids)

(* Entry point of the parser. *)
and entry = (l::~* toplevel) => l

and interpret : bool -> memo2 -> Raw.toplevel -> memo2 =
  fun nodep memo top ->
  let verbose = !verbose && nodep in
  let open Env in
  match top with
  | Sort_def(id,s) ->
      let Ast.Sort s = unsugar_sort s in
      if verbose then
        out "sort %s ≔ %a\n%!" id.elt Print.sort s;
      add_sort id.elt s;
      memo
  | Expr_def(id,s,e) ->
      let Box(s,e) = unsugar_expr e s in
      let ee = Bindlib.unbox e in
      if verbose then
        out "expr %s : %a ≔ %a\n%!" id.elt Print.sort s Print.ex ee;
      add_expr id s e;
      memo
  | Valu_def(id,oc,a,t) ->
      let a = unbox (to_prop (unsugar_expr a _sp)) in
      let t = unbox (to_term (unsugar_expr t _st)) in
      let (a, prf, memo) = type_check id.elt t a memo in
      let v = Eval.eval (Erase.term_erasure t) in
      ignore prf;
      let close = if add_value id oc t a v then "close" else "open" in
      if verbose then
        out "val %s %s : %a\n%!" close id.elt Print.ex a;
      memo
      (* out "  = %a\n%!" Print.ex (Erase.to_valu v); *)
  | Clos_def(b, lids) ->
      let s = if b then "closing" else "opening" in
      let fn lid =
        Printf.printf "%s %s\n%!" s lid.elt;
        try let d = SMap.find lid.elt !env.global_values in
            ignore (Timed.set (Timed.Time.save ()) d.value_clos b)
        with Not_found -> unbound_var lid
      in
      List.iter fn lids;
      memo
  | Chck_sub(a,n,b) ->
      let a = unbox (to_prop (unsugar_expr a _sp)) in
      let b = unbox (to_prop (unsugar_expr b _sp)) in
      if is_subtype a b <> n then raise (Check_failed(a,n,b));
      if verbose then
        begin
          let (l,r) = if n then ("","") else ("¬(",")") in
          out "showed %s%a ⊂ %a%s\n%!" l Print.ex a Print.ex b r;
        end;
      memo
  | Include(fn) ->
      if verbose then
        out "include %S\n%!" fn;
      Log.without (handle_file false) fn;
      memo
  | Def_list(tops) ->
     List.fold_left (interpret nodep) memo tops
  | Glbl_set(l)    ->
      begin
        let open Ast in
        match l with
        | Alvl(b,d) -> Typing.default_auto_lvl := (b,d)
        | Logs s    -> Log.set_enabled s
        | Keep s    -> Equiv.keep_intermediate := true
      end;
      memo
  | Infix(sym,infix) ->
     add_infix sym infix;
     memo

and load_infix : string -> unit = fun fn ->
  (try  Env.load_infix fn
   with Env.Compile ->
     compile_file false fn;
     try Env.load_infix fn
     with Env.Compile -> failwith "source changed during compilation")

and get_memo : string -> memo = fun fn ->
  let fn = Filename.remove_extension fn ^ ".mem" in
  try
    let ch = open_in fn in
    let memo = input_value ch in
    close_in ch;
    memo
  with
    _ -> []

and save_memo : string -> memo -> unit = fun fn memo ->
  let fn = Filename.remove_extension fn ^ ".mem" in
  let ch = open_out fn in
  output_value ch memo;
  close_out ch

and compile_file : bool -> string -> unit = fun nodep fn ->
  if !verbose then out "[%s]\n%!" fn;
  Env.start fn;
  let save = !Env.env in
  Env.env := Env.empty;
  (* avoid timing of grammar compilation *)
  let _ = Grammar.compile entry in
  let ast = Chrono.add_time parsing_chrono parse_file fn in
  let memo = get_memo fn in
  let (_,memo) = List.fold_left (interpret nodep) (memo, []) ast in
  save_memo fn (List.rev memo);
  Env.save_file fn;
  Env.env := save

(* Handling the files. *)
and handle_file : bool -> string -> unit = fun nodep fn ->
  try
    try
      if !recompile && nodep then raise Env.Compile;
      Env.load_file fn
    with Env.Compile ->
        begin
          compile_file nodep fn;
          try Env.load_file fn
          with Env.Compile ->
            failwith "source changed during compilation"
        end
  with
  | Pos.Parse_error(b,p,msg)             ->
     let p = Pos.mk_pos (Input.byte_pos b p)
               (Input.byte_pos b p) (Input.infos b)
     in
     err_msg "%a" print_err_pos p;
     err_msg "No parse.";
     exit 1
  | Unbound_sort(s, p) ->
     if has_pos p then err_msg "%a" print_err_pos p;
     err_msg "Unbound sort %s." s;
     exit 1
  | Sort_clash(t,s)         ->
     if has_pos t.pos then err_msg "%a" print_err_pos t.pos;
     err_msg "Sort %a expected for %a."
       pretty_print_raw_sort s print_raw_expr t;
     exit 1
  | Too_many_args(e)        ->
     if has_pos e.pos then
       err_msg "%a" print_err_pos e.pos;
     err_msg "Expr %a has too many arguments." print_raw_expr e;
     exit 1
  | Unbound_variable(x)   ->
     if has_pos x.pos then err_msg "%a" print_err_pos x.pos;
     err_msg "Unbound variable %s." x.elt;
     exit 1
  | Already_matched(c)      ->
     if has_pos c.pos then err_msg "%a" print_err_pos c.pos;
     err_msg "Variant %s has already been matched." c.elt;
     exit 1

(** Main parsing function taking as input a file name. *)
and parse_file : string -> toplevel list = fun fn ->
  let blank = Regexp.blank_regexp "\\(\\(//[^\n]*\\)\\|[ \t\n\r]*\\)*" in
  let parse f =
    Grammar.parse_file ~utf8:Utf8.UTF8 entry blank f
  in
  List.map (fun act -> act ()) (parse fn)
