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
  let%parser [@layout Lex.noblank] str =
    "\"" (cs:: ~*str_char) "\"" => String.concat "" cs
  in
  str

(* Parser of a module path. *)

let%parser path_atom = (id::RE"[a-zA-Z0-9_]+") => id
let%parser path = (ps:: ~* ((p::path_atom) '.' => p)) (f::path_atom) => ps @ [f]

let path = Grammar.test_after (fun buf pos _ _ ->
               let (c,_,_) = Input.read buf pos in
               c <> '.') path

(* Parser for the contents of a goal. *)
let%parser goal_name = (s::RE"\\([^- \t\n\r]\\|\\(-[^}]\\)\\)+") => s
let%parser goal =
  "{-" (str:: ~* goal_name) "-}" => String.trim (String.concat " " str)

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
let _from_    = Keyword.create "from"
let _if_      = Keyword.create "if"
let _include_ = Keyword.create "include"
let _infix_   = Keyword.create "infix"
let _know_    = Keyword.create "know"
let _let_     = Keyword.create "let"
let _of_      = Keyword.create "of"
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
    (fun buf pos _ _ ->
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

let%parser [@layout Lex.noblank] infix = (i::infix) => i

(* Located identifiers. *)
let%parser llid = (id::lid)                => in_pos _pos id
  ; '(' ((_1,(_2,id,_3,_4,_5))::infix) ')' => id
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
    (id::lid) => in_pos _pos id
  ; '_'       => in_pos _pos "_"

(* Some useful tokens. *)
let%parser elipsis = "⋯" => () ; "..." => ()
let%parser infty   = "∞" => () ; "<inf>" => ()
let%parser arrow   = "→" => ()
let%parser eff     = "p" => Effect.Print
                   ; "c" => Effect.CallCC
                   ; "l" => Effect.Loop
let%parser impl    = "⇒" => Effect.bot
                   ; "→" => Effect.(known [CallCC;Print])
                   ; "→" "_" "(" (l:: ~* eff) ")" => Effect.(known l)
                   ; "↝" => Effect.top
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

let (<=) = fun p1 p2 ->
  match p1, p2 with
  | _     , HO     -> true
  | Any   ,_       -> true
  | Prp p1, Prp p2 -> p1 <= p2
  | Trm p1, Trm p2 -> p1 <= p2
  | Stk   , Stk    -> true
  | Ord p1, Ord p2 -> p1 <= p2
  | _     , _      -> false

let get_infix_prio u =
  match u.elt with EInfx(_,p) -> p
                 | _ -> 0.0

(*let to_full = function*)
(* Parser for expressions. *)
let%parser [@cache] rec expr (m : mode) =
  (* Any (higher-order function) *)
    (m <= Any) "(" (x::llid) ":" (s::sort) "↦" (e::any) ")"
      => in_pos _pos (EHOFn(x,s,e))
  (* Higher-order application *)
  ; (m <= HO && m <> Ord E) (e::expr HO) (args::ho_args)
      => in_pos _pos (EHOAp(e, new_sort_uvar None, args))
  (* Variable *)
  ; (m <= HO) (id::llid) (s:: ~? ('^' (e::expr (Ord E)) => e))
      => begin
           match s with
           | None   -> evari (Some _pos) id
           | Some s -> let id = make id.pos (id.elt ^ "#") in
                       let x = evari (Some id_pos) id in
                       in_pos _pos (EHOAp(x, new_sort_uvar None, [s]))
         end
  (* Parenthesis niveau HO *)
  ; (m = HO) '(' (e::any) ')'
      => (match e.elt  with EInfx(e,_) -> e | _ -> e)

  (* Proposition (boolean type) *)
  ; (m <= Prp A) _bool_
      => p_bool (Some _pos)
  (* Proposition (implication) *)
  ; (m <= Prp F) (a::expr (Prp P)) (t::impl) (b::prop)
      => in_pos _pos (EFunc(t,a,b))
  (* Proposition (tuple type) *)
  ; (m <= Prp P) (a::expr (Prp R)) (bs:: ~+ (prod (b::expr (Prp R)) => b))
      => tuple_type _pos (a::bs)
  (* Proposition (non-empty product) *)
  ; (m <= Prp A) "{" (fs::~+ [semi] ((l::llid) ":" (a::prop) => (l,a))) (s::strict) "}"
      => in_pos _pos (EProd(fs,s))
  (* Proposition (extensible empty record) *)
  ; (m <= Prp A) "{" elipsis "}"
      => in_pos _pos (EProd([],false))
  (* Proposition / Term (empty product / empty record) *)
  ; (m <= HO) "{" "}" (* HO level to avoid ambiguity *)
      => in_pos _pos EUnit
  (* Proposition (disjoint sum) *)
  ; (m <= Prp A) "[" (fs::~+ [semi] ((l::luid) (a::~? (_of_ (a::prop) => a)) => (l,a))) "]"
      => in_pos _pos (EDSum(fs))
  (* empty type *)
  ; (m <= Prp A) empty_s
      => in_pos _pos (EDSum [])
  (* Proposition (universal quantification) *)
  ; (m <= Prp F) "∀" (x::llid) (xs::~* llid) (s::~? (':' (s::sort) => s)) ',' (a::prop)
      => euniv _pos x xs s a
  (* Proposition (dependent function type) *)
  ; (m <= Prp F) "∀" (x::llid) (xs::~* llid) "∈" (a::prop) ',' (b::prop)
      => euniv_in _pos x xs a b
  (* Proposition (existential quantification) *)
  ; (m <= Prp F) "∃" (x::llid) (xs::~* llid) (s::~? (':' (s::sort) => s)) ',' (a::prop)
      => eexis _pos x xs s a
  (* Proposition (dependent pair) *)
  ; (m <= Prp F) "∃" (x::llid) (xs::~* llid) "∈" (a::prop) ',' (b::prop)
      => eexis_in _pos x xs a b
  (* Proposition (set type) *)
  ; (m <= Prp A) "{" (x::llid) "∈" (a::prop) "}"
      => esett _pos x a
  (* Proposition (least fixpoint) *)
  ; (m <= Prp F) "μ" (o:: ~? [none EConv] ('_' (o::ordinal) => o)) ((x,s)::s_arg) ',' (a::any)
      => (let s = match s with Some s -> s | None -> new_sort_uvar (Some x) in
         in_pos _pos (EFixM(s,o,x,a)))
  (* Proposition (greatest fixpoint) *)
  ; (m <= Prp F) "ν" (o:: ~? [none EConv] ('_' (o::ordinal) => o)) ((x,s)::s_arg) ',' (a::any)
      => (let s = match s with Some s -> s | None -> new_sort_uvar (Some x) in
         in_pos _pos (EFixN(s,o,x,a)))
  (* Proposition (membership) *)
  ; (m <= Prp M) (t::expr (Trm I)) memb (a::expr (Prp M))
      => in_pos _pos (EMemb(t,a))
  (* Proposition (restriction) *)
  ; (m <= Prp R) (a::expr (Prp M)) rest (e::cond true)
      => in_pos _pos (ERest(Some a,e))
  (* Proposition (equivalence) *)
  ; (m <= Prp A) (e::cond false)
      => in_pos _pos (ERest(None,e))
  (* Proposition (implication) *)
  ; (m <= Prp R) (e::cond true) simpl (a::expr (Prp M))
      => in_pos _pos (EImpl(e, Some a))
  (* Proposition (parentheses) *)
  ;  (m <= Prp A) "(" (e::expr (Prp F')) ")"
      => (match e.elt  with EInfx(e,_) -> e | _ -> e)
  (* Proposition (injection of term) *)
  ; (m <= Prp A && m <> Any && m <> Prp F') (t::expr (Trm I))
      => begin
          match t.elt with
            | EVari _ | EHOAp _ | EUnit -> Lex.give_up ()
            | _                         -> t
         end

  (* Term (lambda abstraction) *)
  ; (m <= Trm A) _fun_ (args::~+ arg) '{' (t::term) '}'
      => in_pos _pos (ELAbs((List.hd args, List.tl args),t))
  ; (m <= Trm S) _take_ (args::~+ arg) ';' (t::expr (Trm S))
      => in_pos _pos (ELAbs((List.hd args, List.tl args),t))
  ; (m <= Trm S) _suppose_ (props::~+ [comma] (expr (Prp F))) ';' (t::expr (Trm S))
      => suppose _pos props t
  ; (m <= Trm R) lambda (args::~+ arg) '.' (t::expr (Trm I))
      => in_pos _pos (ELAbs((List.hd args, List.tl args),t))
  (* Term (constructor) *)
  ; (m <= Trm A) (c::luid) (t::~? ('[' (t::term) ']' => t))
      => in_pos _pos (ECons(c, Option.map (fun t -> (t, ref `T)) t))
  (* Term (empty list) *)
  ; (m <= Trm A) '[' ']'
      => v_nil _pos
  (* Term ("int") *)
  ; (m <= Trm A) (n::int)
      => from_int _pos n
  (* Term (infix symbol) *)
  ; (m <= Trm I) ((pl',t)>:((t::expr (Trm I)) => (get_infix_prio t,t))) (s::"::")
      (u::(let p = 5.0 in
      if pl' > p -. epsilon then Lex.give_up ();
      expr (Trm I))) => (
        let p = 5.0 in
        let pr' = get_infix_prio u in
        if pr' > p then Lex.give_up ();
        let t =
          in_pos _pos (ECons(in_pos s_pos "Cons",
            Some (record _pos [(none "hd", Some t)
                              ; (none "tl", Some u)], ref `T)))
        in
        in_pos _pos (EInfx(t,p)))
  ; (m <= Trm I) ((pl',t)>:((t::expr (Trm I)) => (get_infix_prio t,t))) ((pl,(s,__,p,pr,ho))>:infix)
      (u::(
      if pl' > pl then Lex.give_up ();
      expr (Trm I)))
    => (let pr' = get_infix_prio u in
         if pr' > pr then Lex.give_up ();
         let t =
           if ho then
             let sort = none (SFun(_st, none (SFun(_st,_st)))) in
             in_pos _pos (EHOAp(s, sort, [t;u]))
           else
             in_pos _pos (EAppl(none (EAppl(s,t)), u)) in
         in_pos _pos (EInfx(t,p)))
  (* Term (record) *)
  ; (m <= Trm A) "{" (fs::~+ [semi] field) "}"
      => record _pos fs
  (* Term (tuple) *)
  ; (m <= Trm A) '(' (t::term) "," (ts::~+ [comma] term) ')'
      => tuple_term _pos (t::ts)
  (* Term (scisors) *)
  ; (m <= Trm A) scis
      => in_pos _pos EScis
  (* Term (application) *)
  ; (m <= Trm P) (t::expr (Trm P)) (u::expr (Trm A))
      => in_pos _pos (EAppl(t,u))
  (* Term (let binding) *)
  ; (m <= Trm S) _let_ (r::v_rec) (arg::let_arg) '=' (t::expr (Trm R)) ';' (u::expr (Trm S))
      => let_binding _pos r arg t u
  (* Term (sequencing). *)
  ; (m <= Trm S) (t::expr (Trm R)) ';' (u::expr (Trm S))
      => in_pos _pos (ESequ(t,u))
  (* Term (mu abstraction) *)
  ; (m <= Trm A) _save_ (arg::llid) '{' (t::term) '}'
      => in_pos _pos (EMAbs(arg,t))
  (* Term (name) *)
  ; (m <= Trm I) _restore_ (s::stack) (t::expr (Trm P))
      => in_pos _pos (EName(s,t))
  (* Term (projection) *)
  ; (m <= Trm A) (t::expr (Trm A)) "." (l::((l::llid) => l ; (l::lnum) => l))
      => in_pos _pos (EProj(t, ref `T, l))
  (* Term (case analysis) *)
  ; (m <= Trm A) _case_ (t::term) '{'
      (ps::~* ((~? '|') (p::patt) arrow (t::term) => (p,t)))
      '}'
      => pattern_matching _pos t ps
  (* Term (conditional) *)
  ; (m <= Trm A) _if_ (c::term) '{' (t::term) '}' (e::~? (_else_ '{' (t::term) '}' => t))
      => if_then_else _pos c t e
  (* Term (replacement) *)
  ; (m <= Trm R) _check_ (u::((e::expr (Trm R)) => e ; '{' (t::term) '}' => t))
      _for_ (t::((e::expr (Trm R)) => e ; '{' (t::term) '}' => t))
            (b::~? justification)
      => in_pos _pos (ERepl(t,u,b))
  (* Term (totality by purity) *)
  ; (m <= Trm R) _delim_ '{' (u::term) '}'
      => in_pos _pos (EDelm(u))
  (* Term ("show" tactic) *)
  ; (m <= Trm R) deduce (a::prop) (p::~? justification)
      => show _pos a p
  (* Term ("show" tactic, sequences of eqns) *)
  ; (m <= Trm R) deduce (a::term) (eqns::~+( equiv
                           (b::expr (Trm R))
                           (p::~? justification)
                              => (_pos,b,p)))
      => (if Pervasives.(List.length eqns <= 1) then Lex.give_up ();
         equations _pos a_pos a eqns)
  (* Term ("use" tactic) *)
  ; (m <= Trm R) _use_ (t::expr (Trm R))
      => use _pos t
  (* Term ("showing" tactic) *)
  ; (m <= Trm S) from (a::expr (Prp R))
         (q::~? (because (q::((e::expr (Trm R)) => e ; '{' (t::term) '}' => t)) => q))
         ';' (p::expr (Trm S))
      => showing _pos a q p
  (* Term ("assume"/"know" tactic) *)
  ; (m <= Trm S) (_assume_ => (); _know_ => ())  (a::expr (Trm R))
         (q::~? (because (q::((e::expr (Trm R)) => e ; '{' (t::term) '}' => t)) => q))
         ';' (p::expr (Trm S))
      => assume _pos a q p
  (* Term ("QED" tactic) *)
  ; (m <= Trm A) _qed_
      => qed _pos
  (* Term (fixpoint) *)
  ; (m <= Trm A) _fix_ (arg::arg) '{' (t::term) '}'
      => (let (a,ao) = arg in
         let t = in_pos _pos (EFixY(a,t)) in
         let t = match ao with
           | None -> t
           | Some ty -> in_pos _pos (ECoer(new_sort_uvar None,t,ty))
         in
         t)
  (* Term (printing) *)
  ; (m <= Trm A) _print_ (s::str_lit)
      => in_pos _pos (EPrnt(s))
  (* Term (type coersion) *)
  ; (m <= Trm A) "(" (t::term) ":" (a::prop) ")"
      => in_pos _pos (ECoer(new_sort_uvar None,t,a))
  (* Term (auto lvl) *)
  ; (m <= Trm S) _set_ (l::set_param) ';' (t::expr (Trm S))
      => in_pos _pos (EPSet(new_sort_uvar None,l,t))
  (* Term (let such that) *)
  ; ( m <= Trm S) _let_ (vs::s_lst) _st_ (x::llid_wc) ':' (a::prop) ';' (u::expr (Trm S))
      => esuch _pos vs x a u
  (* Term (parentheses) *)
  ; (m <= Trm A) "(" (t::term) ")"
      => (match t.elt  with EInfx(t,_) -> t | _ -> t)

  (* Ordinal (infinite) *)
  ; (m <= Ord E) infty
      => in_pos _pos EConv
  (* Ordinal (successor) *)
  ; (m <= Ord F) (o::ordinal) "+ₒ" (n::int)
      => in_pos _pos (ESucc(o,n))
  (* Ordinal (parenthesis) *)
  ; (m <= Ord E) '(' (o::ordinal) ')'
      => (match o.elt  with EInfx(o,_) -> o | _ -> o)
  (* Goal (term or stack) *)
  ; (m <= Stk || m <= Trm A) (s::goal)
      => in_pos _pos (EGoal(s))

and justification =
  because (p::((t::expr (Trm R)) => t ; '{' (t::term)  '}' => t)) => p

and cond opt =
    (opt = true) (t::expr (Trm I))
            => (let u = none (ECons(none "true", None))
               in EEquiv(t,true,u))
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
  ; _val_ (r::v_rec) (id::llid) ':' (a::prop) '=' (t::term)
      => (fun () -> val_def r id a t)

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

(* Entry point of the parser. *)
and entry = (l::~* toplevel) => l

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
        | Keep s    -> Equiv.keep_intermediate := true
      end;
  | Infix(sym,infix) ->
     add_infix sym infix

and load_infix : string -> unit = fun fn ->
  (try  Env.load_infix fn
   with Env.Compile ->
     compile_file false fn;
     try Env.load_infix fn
     with Env.Compile -> failwith "source changed during compilation")

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
     begin
        let p = Pos.get_pos b p in
        let p = Pos.{ start = p; end_ = p } in
        err_msg "No parse %a." print_short_pos p;
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
        err_msg "Unbound sort %s (%a)." s print_short_pos p;
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
                        pretty_print_raw_sort s print_short_pos p;
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
                        print_short_pos p;
                      Quote.quote_file stderr p
        in
        exit 1
      end
  | Already_matched(c)      ->
      begin
        match c.pos with
        | None   -> err_msg "%s has already been matched." c.elt;
        | Some p -> err_msg "%s (%a) has already been matched." c.elt
                      print_short_pos p;
                    Quote.quote_file stderr p
      end;
      exit 1

(** Main parsing function taking as input a file name. *)
and parse_file : string -> toplevel list = fun fn ->
  let blank = Regexp.blank_regexp "\\(\\(//[^\n]*\\)\\|[ \t\n\r]*\\)*" in
  let parse f =
    let ch = open_in f in
    let r = Grammar.parse_channel ~utf8:Utf8.UTF8 ~filename:f entry blank ch in
    close_in ch;
    r
  in
  List.map (fun act -> act ()) (parse fn)
