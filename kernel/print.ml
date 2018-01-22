(** Printing functions for expressions. *)

open Bindlib
open Ptr
open Sorts
open Pos
open Ast
open Output
open Printf
open Uvars
open Priority

let print_map : (string * 'a) printer -> string -> 'a A.t printer =
  fun pelem sep ch m -> print_list pelem sep ch (A.bindings m)

let rec sort : type a. a sort printer = fun ch s ->
  match s with
  | V      -> output_string ch "ι"
  | T      -> output_string ch "τ"
  | S      -> output_string ch "σ"
  | P      -> output_string ch "ο"
  | O      -> output_string ch "κ"
  | F(a,b) -> let (l,r) = match a with F(_,_) -> ("(",")") | _ -> ("","") in
              fprintf ch "%s%a%s→%a" l sort a r sort b

let print_vars ch e =
  let vars = uvars e in
  match vars with
  | [] -> ()
  | U (_,x)::l -> fprintf ch "(?%d%t)" x.uvar_key
                    (fun ch -> List.iter (function U (_,x) ->
                                   fprintf ch ",?%d" x.uvar_key) l)

let arrow ch t =
  let open Totality in
  match norm t with
  | Tot   -> fprintf ch "⇒"
  | Ter   -> fprintf ch "→"
  | Any   -> fprintf ch "↝"
  | Unk _ -> fprintf ch "?>"
  | Max _ -> fprintf ch "?>"

let rec ex : type a. mode -> a ex loc printer = fun pr ch e ->
  let is_unit : v ex loc -> bool = fun e ->
    match (Norm.repr e).elt with
    | Reco(m)   -> m = A.empty
    | _         -> false
  in
  let is_eq : p ex loc -> (t ex loc * string * t ex loc) option = fun e ->
    match (Norm.repr e).elt with
    | Rest({elt=Memb({elt=Valu r},{elt=Prod m})},Equiv(e1,b,e2))
    | Memb({elt=Valu r},{elt=Rest({elt=Prod m},Equiv(e1,b,e2))}) ->
       if is_unit r && m = A.empty then
         let s = if b then "≡" else "!=" in
         Some(e1,s,e2)
       else None
    | _ -> None
  in
  let e = Norm.repr e in
  let exa ch t = ex Any ch t in
  let exp ch t = ex (Prp F) ch t in
  let ext ch t = ex (Trm F) ch t in
  let exi ch t = ex (Trm I) ch t in
  let exo ch t = ex (Ord F) ch t in
  match e.elt with
  | Vari(_,x)   -> output_string ch (name_of x)
  | HFun(s,_,b) -> let (x,t) = unbind (mk_free s) (snd b) in
                   fprintf ch "(%s ↦ %a)" (name_of x) exa t
  | HApp(_,f,a) -> let rec print_app : type a b.(a -> b) ex loc -> unit =
                     fun f ->
                       let f = Norm.repr f in
                       match f.elt with
                       | HApp(_,g,a) -> print_app g; fprintf ch "%a,"
                                                             exa a
                       | _           -> fprintf ch "%a<" (ex HO) f
                   in
                   print_app f; fprintf ch "%a>" exa a
  | HDef(_,d)   -> output_string ch d.expr_name.elt
  | Func(t,a,b) -> let (l,r) = if Prp P <= pr then ("(",")") else ("","") in
                   fprintf ch "%s%a%s %a %a" l (ex (Prp P)) a r arrow t exp b
  | Prod(m)     -> let pelt ch (l,(_,a)) =
                     fprintf ch "%s : %a" l exp a
                   in fprintf ch "{%a}" (print_map pelt "; ") m
  | DSum(m)     -> let pelt ch (l,(_,a)) =
                     fprintf ch "%s : %a" l exp a
                   in fprintf ch "[%a]" (print_map pelt "; ") m
  | Univ(s,b)   -> let (x,a) = unbind (mk_free s) (snd b) in
                   fprintf ch "∀%s:%a, %a" (name_of x)
                     sort s exp a
  | Exis(s,b)   -> let (x,a) = unbind (mk_free s) (snd b) in
                   fprintf ch "∃%s:%a, %a" (name_of x)
                     sort s exp a
  | FixM(o,b)   -> let (x,a) = unbind (mk_free P) (snd b) in
                   fprintf ch "μ^%a %s, %a"
                           exo o (name_of x) exp a
  | FixN(o,b)   -> let (x,a) = unbind (mk_free P) (snd b) in
                   fprintf ch "ν^%a %s, %a"
                           exo o (name_of x) exp a
  | Memb(t,a)   -> begin
                     match is_eq e with
                     | Some(e1,s,e2) -> fprintf ch "%a%s%a" exi e1 s exi e2
                     | None ->
                       let (l,r) = if Prp M <= pr then ("(",")") else ("","") in
                       fprintf ch "%a ∈ %s%a%s" exi t l (ex (Prp M)) a r
                   end
  | Rest(a,c)   -> begin
                     match is_eq e with
                     | Some(e1,s,e2) -> fprintf ch "%a%s%a" exi e1 s exi e2
                     | None ->
                       let (l,r) = if Prp R <= pr then ("(",")") else ("","") in
                       fprintf ch "(%s%a%s | %a)" l (ex (Prp R)) a r rel c
                   end
  | Impl(e,a)   -> fprintf ch "%a ↪ %a" rel e (ex (Prp R)) a (* FIXME, no parsing for Impl ? *)
  | LAbs(ao,b)  -> let (x,t) = unbind (mk_free V) (snd b) in
                   begin (* FIXME: group binders *)
                     match ao with
                     | None   -> fprintf ch "fun %s {%a}"
                                         (name_of x) ext t
                     | Some a -> fprintf ch "fun (%s:%a) {%a}"
                                         (name_of x) exp a ext t
                   end
  | Cons(c,v)   -> if is_unit v then fprintf ch "%s" c.elt
                   else fprintf ch "%s[%a]" c.elt ext v
  | Reco(m)     -> let pelt ch (l,(_,a)) =
                     fprintf ch "%s = %a" l ext a
                   in fprintf ch "{%a}" (print_map pelt "; ") m
  | Scis        -> output_string ch "✂"
  | VDef(d)     -> output_string ch d.value_name.elt
  | Valu(v)     -> ex pr ch v
  | Appl(t,u)   -> let (l,r) = if Trm P < pr then ("(",")") else ("","") in
                   fprintf ch "%s%a %a%s" l (ex (Trm P)) t (ex (Trm A)) u r
  | MAbs(b)     -> let (x,t) = unbind (mk_free S) (snd b) in
                   fprintf ch "save %s {%a}" (name_of x) ext t
  | Name(s,t)   -> fprintf ch "restore %a %a" exa s ext t
  | Proj(v,l)   -> fprintf ch "%a.%s" (ex (Trm A)) v l.elt
  | Case(v,m)   -> let pelt ch (c, (_, (_,b))) =
                     let (x,t) = unbind (mk_free V) b in
                     fprintf ch "%s[%s] → %a"
                             c (name_of x) ext t
                   in
                   let pcase = print_map pelt " " in
                   fprintf ch "case %a {%a}" ext v pcase m
  | FixY(sf,b)  -> let (x,t) = unbind (mk_free T) (snd b) in
                   let sf = if sf then "" else "unsafe " in
                   fprintf ch "fix %s%s {%a}" sf (name_of x) ext t
  | Prnt(s)     -> fprintf ch "print(%S)" s
  | Repl(t,u)   -> fprintf ch "(check %a for %a)" ext t ext u (* FIXME *)
  | Delm(t)     -> fprintf ch "delim {%a}" ext t
  | Conv        -> output_string ch "∞"
  | Succ(o)     -> fprintf ch "%a+1" exo o
  | Coer(_,e,a) -> fprintf ch "(%a : %a)" ext e exp a
  | Such(_,_,r) ->
      output_string ch "let ";
      let rec aux : type a b. (a, prop * b ex loc) bseq -> unit = fun seq ->
        match seq with
        | BLast(s,b) ->
            let (x,(a,t)) = unbind (mk_free s) b in
            fprintf ch "%s:%a s.t. " (name_of x) sort s;
            let _ =
              match r.opt_var with
              | SV_None    -> output_string ch "_"
              | SV_Valu(v) -> ext ch v
              | SV_Stac(s) -> exa ch s
            in
            fprintf ch " : %a in %a" exp a ext t
        | BMore(s,b) ->
            let (x,seq) = unbind (mk_free s) b in
            fprintf ch "%s:%a, " (name_of x) sort s;
            aux seq
      in aux r.binder
  | PSet(l,s,e) -> fprintf ch "%a; %a" print_set_param l ext e (* FIXME *)
  | ITag(_,i)   -> fprintf ch "#%i" i
  | Dumm(_)     -> output_string ch "∅"
  | VWit(w)     -> fprintf ch "%s%a" w.name print_vars e
  | SWit(w)     -> fprintf ch "%s%a" w.name print_vars e
  | UWit(w)     -> fprintf ch "%s%a" w.name print_vars e
  | EWit(w)     -> fprintf ch "%s%a" w.name print_vars e
  | OWMu(w)     -> fprintf ch "%s%a" w.name print_vars e
  | OWNu(w)     -> fprintf ch "%s%a" w.name print_vars e
  | OSch(i,_,w) -> fprintf ch "%s%a" w.name.(i) print_vars e
  | UVar(_,u)   -> fprintf ch "?%i" u.uvar_key
  | Goal(_,s)   -> fprintf ch "{- %s -}" s
  | VPtr(p)     -> fprintf ch "VPtr(%a)" VPtr.print p
  | TPtr(p)     -> fprintf ch "TPtr(%a)"  Ptr.print p

and print_set_param ch = function
  | Alvl(b,d)   -> fprintf ch "auto %d %d" b d
  | Logs(s)     -> fprintf ch "log %s" s

and rel ch cnd =
  let eq b = if b then "=" else "≠" in
    match cnd with
    | Equiv(t,b,u) -> fprintf ch "%a %s %a" (ex (Trm F)) t (eq b) (ex (Trm F)) u
    | NoBox(v)     -> fprintf ch "%a↓" (ex (Trm F)) v

let ex ch t = ex Any ch t

let print_fix_sch ch sch =
  let (x,t) = unbind (mk_free T) (snd (fst sch.fsch_judge)) in
  let (vars,k) = unmbind (mk_free O) (snd sch.fsch_judge) in
  let vars = Array.map (fun x -> Pos.none (mk_free O x)) vars in
  let print_vars = print_list ex "," in
  fprintf ch "%a (⊢ λx.Y(λ%s.%a,x) : %a)" print_vars (Array.to_list vars)
    (name_of x) ex t ex k

let print_sub_sch ch sch =
  let (vars,(k1,k2)) = unmbind (mk_free O) sch.ssch_judge in
  let vars = Array.map (fun x -> Pos.none (mk_free O x)) vars in
  let print_vars = print_list ex "," in
  let rel = List.map (fun (i,j) -> (vars.(i), vars.(j))) sch.ssch_relat in
  let print_cmp ch (i,j) = fprintf ch "%a<%a" ex i ex j in
  let print_rel = print_list print_cmp "," in
  fprintf ch "%a (%a ⊢ %a < %a)" print_vars (Array.to_list vars)
    print_rel rel ex k1 ex k2

let print_sch ch sch =
  match sch with
  | FixSch sch -> print_fix_sch ch sch
  | SubSch sch -> print_sub_sch ch sch

let omb ch b =
  let (vars,k) = unmbind (mk_free O) b in
  let vars = Array.map (fun x -> Pos.none (mk_free O x)) vars in
  let print_vars = print_list ex "," in
  fprintf ch "%a.%a" print_vars (Array.to_list vars) ex k

let rec get_lambda_name : type a. a ex loc -> string =
  fun e ->
    let e = Norm.whnf e in
    match e.elt with
    | LAbs(_,b) -> (bndr_name b).elt
    | VDef(d)   -> get_lambda_name (d.value_eras)
    | HDef(_,d) -> get_lambda_name (d.expr_def)
    | Valu(v)   -> get_lambda_name v
    | _         -> "x"

let rec get_case_name : type a. A.key -> a ex loc -> string =
  fun k e ->
    let e = Norm.whnf e in
    match e.elt with
    | Case(_,c) ->
       begin
         try
           let (_,f) = A.find k c in
           (bndr_name f).elt
         with Not_found -> "x"
       end
    | VDef(d)   -> get_case_name k (d.value_eras)
    | HDef(_,d) -> get_case_name k (d.expr_def)
    | Valu(v)   -> get_case_name k v
    | _         -> "x"
