#define LOCATE locate

open Pos
open Blank
open Raw

let lsep s elt =
  parser
  | EMPTY                      -> []
  | e:elt es:{_:STR(s) elt}* $ -> e::es

let lsep_ne s elt =
  parser
  | e:elt es:{_:STR(s) elt}* $ -> e::es

module KW =
  struct
    let keywords = Hashtbl.create 20
    let is_keyword : string -> bool = Hashtbl.mem keywords

    let check_not_keyword : string -> unit = fun s ->
      if is_keyword s then Decap.error ()

    let new_keyword : string -> unit Decap.grammar = fun s ->
      let ls = String.length s in
      if ls < 1 then raise (Invalid_argument "invalid keyword");
      if is_keyword s then raise (Invalid_argument "keyword already defied");
      Hashtbl.add keywords s s;
      let f str pos =
        let str = ref str in
        let pos = ref pos in
        for i = 0 to ls - 1 do
          let (c,str',pos') = Input.read !str !pos in
          if c <> s.[i] then Decap.error ();
          str := str'; pos := pos'
        done;
        let (c,_,_) = Input.read !str !pos in
        match c with
        | 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' | '\'' -> Decap.error ()
        | _                                           -> ((), !str, !pos)
      in
      Decap.black_box f (Charset.singleton s.[0]) false s
  end

let parser lid = id:''[a-z][a-zA-Z0-9_']*'' -> KW.check_not_keyword id; id
let parser uid = id:''[A-Z][a-zA-Z0-9_']*'' -> KW.check_not_keyword id; id

let parser llid = id:lid -> in_pos _loc id
let parser luid = id:uid -> in_pos _loc id

let _sort_ = KW.new_keyword "sort"
let _def_  = KW.new_keyword "def"
let _val_  = KW.new_keyword "val"
let _fun_  = KW.new_keyword "fun"
let _save_ = KW.new_keyword "save"
let _case_ = KW.new_keyword "case"
let _of_   = KW.new_keyword "of"
let _fix_  = KW.new_keyword "fix"

let parser arrow = "→" | "->"
let parser impl  = "⇒" | "=>"
let parser scis  = "✂" | "8<"
let parser equiv =
  | {"≡" | "="} -> true 
  | "≠"         -> false

(** Parser for sorts. *)
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
let sort = sort `F

(** Parser for expressions *)
type p_prio = [`A | `F]
type t_prio = [`A | `Ap | `F]

type mode = [`Any | `Prp of p_prio | `Trm of t_prio | `Stk | `Ord ]

let parser expr (m : mode) =
  (* Any (higher-order function) *)
  | "(" x:llid s:{":" s:sort} "↦" e:(expr `Any)
      when m = `Any
      -> in_pos _loc (EHOFn(x,s,e))

  (* Proposition (variable and higher-order application) *)
  | id:llid args:{"(" (lsep "," (expr `Any)) ")"}?[[]]
      when m = `Prp`A
      -> in_pos _loc (EVari(id, args)) 
  (* Proposition (implication) *)
  | a:(expr (`Prp`A)) impl b:(expr (`Prp`F))
      when m = `Prp`F
      -> in_pos _loc (EFunc(a,b))
  (* Proposition (non-empty product) *)
  | "{" fs:(lsep_ne ";" (parser l:llid ":" a:(expr (`Prp`F)))) "}"
      when m = `Prp`A
      -> in_pos _loc (EProd(fs))
  (* Proposition / Term (empty product / empty record) *)
  | "{" "}"
      when m = `Prp`A || m = `Trm`A
      -> in_pos _loc EUnit
  (* Proposition (disjoint sum) *)
  | "[" fs:(lsep ";" (parser l:luid _:_of_ a:(expr (`Prp`F)))) "]"
      when m = `Prp`A
      -> in_pos _loc (EDSum(fs))
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

  (* Term (variable and higher-order application) *)
  | id:llid args:{"(" (lsep "," (expr `Any)) "}"}?[[]]
      when m = `Trm`A
      -> in_pos _loc (EVari(id, args)) 
  (* Term (lambda abstraction) *)
  | _fun_ args:fun_arg+ arrow t:(expr (`Trm`F))
      when m = `Trm`F
      -> in_pos _loc (ELAbs((List.hd args, List.tl args),t))
  | "λ" args:fun_arg+ "." t:(expr (`Trm`F))
      when m = `Trm`F
      -> in_pos _loc (ELAbs((List.hd args, List.tl args),t))
  (* Term (constructor) *)
  | c:luid "[" t:(expr (`Trm`F))? "]"
      when m = `Trm`A 
      -> in_pos _loc (ECons(c, Util.map_opt (fun t -> (t, ref `T)) t))
  (* Term (record) *)
  | "{" fs:(lsep_ne ";" (parser l:llid "=" a:(expr (`Trm`F)))) "}"
      when m = `Trm`A
      -> in_pos _loc (EReco(List.map (fun (l,a) -> (l, a, ref `T)) fs))
  (* Term (scisors) *)
  | scis
      when m = `Trm`A
      -> in_pos _loc EScis
  (* Term (application) *)
  | t:(expr (`Trm`Ap)) u:(expr (`Trm`F))
      when m = `Trm`Ap
      -> in_pos _loc (EAppl(t,u))
  (* Term (mu abstraction) *)
  | _save_ args:fun_arg+ arrow t:(expr (`Trm`F))
      when m = `Trm`F
      -> in_pos _loc (EMAbs((List.hd args, List.tl args),t))
  | "μ" args:fun_arg+ "." t:(expr (`Trm`F))
      when m = `Trm`F
      -> in_pos _loc (EMAbs((List.hd args, List.tl args),t))
  (* Term (name) *)
  | "[" s:(expr `Stk) "]" t:(expr (`Trm`F))
      when m = `Trm`F
      -> in_pos _loc (EName(s,t))
  (* Term (projection) *)
  | t:(expr (`Trm`A)) "." l:llid
      when m = `Trm`A
      -> in_pos _loc (EProj(t, ref `T, l))
  (* Term (case analysis) *)
  | _case_ t:(expr (`Trm`F)) _of_ ps:pattern*
      when m = `Trm`F
      -> in_pos _loc (ECase(t, ref `T, ps))
  | "[" "?" t:(expr (`Trm`F)) ps:pattern* "]"
      when m = `Trm`A
      -> in_pos _loc (ECase(t, ref `T, ps))
  (* Term (fixpoint) *)
  | _fix_ t:(expr (`Trm`F))
      when m = `Trm`F
      -> in_pos _loc (EFixY(t))
  (* Term (type coersion) *)
  | "(" t:(expr (`Trm`F)) ":" a:(expr (`Prp`F)) ")"
      when m = `Trm`A
      -> in_pos _loc (ECoer(t,a))
  (* Term (type abstraction) *)
  | "Λ" "(" x:llid ":" s:sort ")" t:(expr (`Trm`F))
      when m = `Trm`F
      -> in_pos _loc (ELamb(x,s,t))
  (* Term (parentheses) *)
  | "(" t:(expr (`Trm`F)) ")"
      when m = `Trm`A
  (* Term (level coersions) *)
  | (expr (`Trm`A))
      when m = `Trm`Ap
  | (expr (`Trm`Ap))
      when m = `Trm`F
  (* Term (from anything) *)
  | (expr (`Trm`F))
      when m = `Any

  (* Stack (variable and higher-order application) *)
  | id:llid args:{"(" (lsep "," (expr `Any)) "}"}?[[]]
      when m = `Stk
      -> in_pos _loc (EVari(id, args)) 
  (* Stack (empty) *)
  | "ε"
      when m = `Stk
      -> in_pos _loc EEpsi
  (* Stack (push) *)
  | v:(expr (`Trm`A)) {"." | "·"} s:(expr `Stk)
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
and fun_arg =
  | id:llid                               -> (id, None  )
  | "(" id:llid ":" a:(expr (`Prp`A)) ")" -> (id, Some a)
and pattern =
  | "|" c:luid "[" x:llid a:{":" (expr (`Prp`F))}? "]" arrow t:(expr (`Trm`F)) 
    -> (c, (x,a), t)
let expr = expr `Any

(** Toplevel. *)
let parser toplevel =
  | _sort_ id:llid '=' s:sort
    -> Sort_def(id,s)
  | _def_  id:llid args:sort_arg* s:{':' sort}? '=' e:expr
    -> let s = sort_from_opt s in
       let f (id,s) e = Pos.none (EHOFn(id,s,e)) in
       let e = List.fold_right f args e in
       let f (_ ,a) s = Pos.none (SFun(a,s)) in
       let s = List.fold_right f args s in
       Expr_def(id,s,e)
  | _val_  id:llid ao:{':' expr}? '=' t:expr
    -> Valu_def(id, ao, t)
and sort_arg =
  | id:llid                    -> (id, new_sort_uvar ())
  | "(" id:llid ":" s:sort ")" -> (id, s)

let parse_file =
  let open Decap in
  handle_exception (parse_file (parser toplevel*) blank)
