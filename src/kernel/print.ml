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
  let open Effect in
  match complete t with
  | Some l -> (match List.mem Loop l, List.mem CallCC l with
              | false, false -> fprintf ch "⇒"
              | true , false -> fprintf ch "⇏"
              | false, true  -> fprintf ch "→"
              | true , true  -> fprintf ch "↛")
  | _        -> fprintf ch "?>"

let print_set_param ch = function
  | Alvl(b,d)   -> fprintf ch "auto %d %d" b d
  | Logs(s)     -> fprintf ch "log %s" s
  | Keep(b)     -> fprintf ch "keep_intermediate %b" b

let hint fn ch = function
  | Eval            -> Printf.fprintf ch "eval"
  | Sugar           -> Printf.fprintf ch "sugar"
  | Close(true,ls)  -> Printf.fprintf ch "close %t;"
                         (fun ch -> List.iter fn ls)
  | Close(false,ls) -> Printf.fprintf ch "open %t;"
                         (fun ch -> List.iter fn ls)
  | Auto b          -> Printf.fprintf ch "auto %b" b
  | LSet l          -> fprintf ch "%a" print_set_param l

let vhint ch = hint (fun v -> Printf.fprintf ch "%s " v.value_name.elt) ch
let lhint ch = hint (fun v -> Printf.fprintf ch "%s " v.elt) ch

let removeq : ('a -> 'a -> bool) -> 'a list ref -> 'a -> bool = fun eq ls x ->
  let rec fn acc = function
    | [] -> false
    | y::l -> if eq x y then (ls := List.rev_append acc l; true)
              else fn (y::acc) l
  in
  fn [] !ls

let collect_exis : type s a.ctxt -> s sort -> a ex loc ->
                        s var list * a ex loc * ctxt =
  fun ctxt s e ->
  let rec fn : type a.ctxt -> s var list -> a ex loc ->
                    s var list * a ex loc * ctxt =
    fun ctxt acc e ->
      let e = Norm.repr e in
      match e.elt with
      | Exis(s', f) ->
         begin
           match eq_sort s s' with
           | Eq.Eq  ->  let ((x:s var), t, ctxt) = bndr_open_in ctxt f in
                        fn ctxt (x::acc) t
           | Eq.NEq -> (acc, e, ctxt)
         end
      | _           -> (acc, e, ctxt)
  in
  fn ctxt [] e

type _ sugar =
  | NoSugar : 'a sugar
  | StrictReco : (pos * prop) Assoc.t * ctxt -> p sugar
  | Tuple      : valu list -> v sugar
  | TupleType  : prop list -> p sugar
  | DepSum     : t var list * prop * prop * ctxt -> p sugar
  | Compr      : t var * prop * rel * ctxt -> p sugar
  | Def        : 'a ex loc -> 'a sugar

let is_comprehension : type a. ctxt -> a ex loc -> a sugar = fun ctxt e ->
  match (Norm.repr e).elt with
  | Exis(T, f) ->
     begin
       let (x, t, ctxt) = bndr_open_in ctxt f in
       match (Norm.repr t).elt with
       | Memb(t,p) ->
          begin
            match ((Norm.repr t).elt, (Norm.repr p).elt) with
            | (Vari(_,y), Rest(p,eq)) when eq_vars x y -> Compr(x,p,eq,ctxt)
            | _                                        -> NoSugar
          end
       | _         -> NoSugar
     end
  | _          -> NoSugar

let is_strict_record : type a. ctxt -> a ex loc -> a sugar =
  fun ctxt e ->
  let (ls, e, ctxt) = collect_exis ctxt V e in
  match e.elt with
  | Memb(t,p) ->
     begin
       match (Norm.repr t).elt with
       | Valu v ->
          begin
            match ((Norm.repr v).elt, (Norm.repr p).elt) with
            | (Reco m1, Prod m2) ->
               if
                 A.length m1 = A.length m2 &&
                   List.length ls = A.length m1 &&
                     let ls = ref ls in
                     A.for_all (fun k (_,v) ->
                         A.mem k m2 &&
                           begin
                             match (Norm.repr v).elt with
                             | Vari(V,x) -> removeq eq_vars ls x
                             | _         -> false
                           end
                       ) m1
               then StrictReco (m2, ctxt)
               else NoSugar

            | _                  -> NoSugar
          end
       | _      -> NoSugar
     end
  | _         -> NoSugar

let is_tuple : type a.a ex loc -> a sugar = fun e ->
  match (Norm.repr e).elt with
  | Reco m ->
     let size = A.length m in
     begin
       try
         let res = ref [] in
         for i = size downto 1 do
           let k = string_of_int i in
           res:= snd (A.find k m) :: !res
         done;
         Tuple !res
       with Not_found -> NoSugar
     end
  | _ -> NoSugar

let is_tuple_type : type a.a ex loc -> a sugar = fun e ->
  match (Norm.repr e).elt with
  | Prod m ->
     let size = A.length m in
     begin
       try
         let res = ref [] in
         for i = size downto 1 do
           let k = string_of_int i in
           res:= snd (A.find k m) :: !res
         done;
         TupleType !res
       with Not_found -> NoSugar
     end
  | _ -> NoSugar

type feq = { mutable eq : 'a. 'a ex loc -> 'a ex loc -> bool }
let feq_expr : feq = { eq = fun _ _ -> assert false }

let is_def : type a. a ex loc -> a sugar = fun e ->
  let rec is_def : type a. a ex loc -> bool = fun e ->
    match (Norm.repr e).elt with
    | VDef _      -> true
    | HDef _      -> true
    | HApp(_,e,_) -> is_def e
    | _           -> false
  in
  (* TODO: uvars e could be non empty, we should just make sure
     variables are not instanciated *)
  if is_def e || uvars e <> [] then NoSugar else
  let (s,e) = Ast.sort e in
  let res : a sugar =
    match s with
    | V ->
       Env.SMap.fold (fun k v acc ->
           match acc with
           | NoSugar when feq_expr.eq e v.value_eras ->
              Def(Pos.none (VDef v))
           | _ -> acc)
         !(Env.env).Env.global_values NoSugar
    | _ -> NoSugar
  in
  if res <> NoSugar then res else
  let is_expr : any_expr -> a sugar = fun (Expr(s',e')) ->
    let rec fn : type b. (unit -> bool) -> b ex loc -> b sort -> a sugar =
      fun test e' s' ->
      match eq_sort s s' with
      | Eq.Eq  -> if feq_expr.eq e e' && test () then Def e' else NoSugar
      | Eq.NEq -> match s' with
                  | F(sa,s') -> let u = { uvar_key = -1
                                        ; uvar_val = ref (Unset [])
                                        ; uvar_pur = ref false} in
                                let v = Pos.none (UVar(sa, u)) in
                                let e' = Pos.none (HApp(sa,e',v)) in
                                let is_set () = match !(u.uvar_val) with
                                  | Unset _ -> false
                                  | _       -> true
                                in
                                let test () = is_set () && test () in
                                fn test e' s'
                  | _        -> NoSugar
    in
    fn (fun _ -> true) (Pos.none (HDef(s',e'))) s'
  in
  Env.SMap.fold (fun k e acc ->
      match acc with NoSugar -> is_expr e | _ -> acc)
    !(Env.env).Env.global_exprs NoSugar

let is_dep_sum : type a.ctxt -> a ex loc -> a sugar = fun ctxt e ->
  let (ls, e, ctxt) = collect_exis ctxt T e in
  let ty = ref None in
  match is_tuple_type e with
  | NoSugar      -> NoSugar
  | TupleType ps ->
     if List.length ps = 1 + List.length ls && List.length ls > 0 then
       try
         let vars = List.mapi (
           fun i x ->
           match (Norm.repr (List.nth ps i)).elt with
           | Memb(y,t) ->
              begin
                match (Norm.repr y).elt with
                | Vari(T,y) when eq_vars x y ->
                   begin
                     match !ty with
                     | None    -> ty := Some t
                     | Some ty -> if not (feq_expr.eq ty t) then raise Exit
                   end;
                   x
                | _                          -> raise Exit
              end
           | _         -> raise Exit) ls
         in
         let ty = match !ty with
           | None    -> assert false
           | Some ty -> ty
         in
         DepSum(vars, ty, List.nth ps (List.length ls),ctxt)
       with
         Exit -> NoSugar
     else NoSugar
  | _ -> assert false

let is_sugar : type a.ctxt -> a ex loc -> a sugar = fun ctxt e ->
  let s = is_strict_record ctxt e in
  if s <> NoSugar then s else
  let s = is_tuple e in
  if s <> NoSugar then s else
  let s = is_dep_sum ctxt e in
  if s <> NoSugar then s else
  let s = is_comprehension ctxt e in
  if s <> NoSugar then s else
  let s = is_def e in
  if s <> NoSugar then s else
  s

let is_unit : v ex loc -> bool = fun e ->
  match (Norm.repr e).elt with
  | Reco(m)   -> m = A.empty
  | _         -> false

let is_unit_ty : ctxt -> p ex loc -> bool = fun ctxt e ->
  match is_strict_record ctxt e with
  | StrictReco(m,_) when m = A.empty -> true
  | _ -> false

let rec ex : type a. ctxt -> mode -> a ex loc printer = fun ctxt pr ch e ->
  let is_eq : p ex loc -> (t ex loc * string * t ex loc) option = fun e ->
    match (Norm.repr e).elt with
    | Rest({elt=Memb({elt=Valu r},{elt=Prod m})},Equiv(e1,b,e2))
    | Memb({elt=Valu r},{elt=Rest({elt=Prod m},Equiv(e1,b,e2))}) ->
       if is_unit r && m = A.empty then
         let s = if b then "≡" else "≠" in
         Some(e1,s,e2)
       else None
    | _ -> None
  in
  let e = Norm.repr e in
  let exa ch t = ex ctxt Any ch t in
  let exp ch t = ex ctxt (Prp F) ch t in
  let ext ch t = ex ctxt (Trm F) ch t in
  let exi ch t = ex ctxt (Trm I) ch t in
  let exo ch t = ex ctxt (Ord F) ch t in
  let supo ch o = match (Norm.repr o).elt with
    | Conv -> ()
    | _    -> fprintf ch "^%a " exo o
  in
  match is_sugar ctxt e with
  | StrictReco (m,c) -> let pelt ch (l,(_,a)) =
                          fprintf ch "%s : %a" l (ex c (Prp F)) a
                        in fprintf ch "{%a}" (print_map pelt "; ") m
  | Tuple ls         -> fprintf ch "(%a)" (print_list ext ", ") ls
  | TupleType ls     -> let (l,r) =
                          if Prp P < pr then ("(",")") else ("","")
                        in
                        fprintf ch "%s%a%s" l
                          (print_list (ex ctxt (Prp R)) " × ") ls r
  | DepSum(l,a,p,c)  -> let pelt ch x = fprintf ch "%s" (name_of x) in
                        fprintf ch "∃%a∈%a, %a"
                          (print_list pelt " ") l exp a (ex c (Prp F)) p
  | Compr(x,p,r,c)   -> fprintf ch "{ %s ∈ %a | %a }"
                          (name_of x) exp p (rel c) r
  | Def e            -> ex ctxt pr ch e
  | NoSugar          ->
  match e.elt with
  | Vari(_,x)   -> output_string ch (name_of x)
  | HFun(s,_,b) -> let (x,t,ctxt) = bndr_open_in ctxt b in
                   fprintf ch "(%s ↦ %a)" (name_of x) (ex ctxt Any) t
  | HApp(_,f,a) -> let rec print_app : type a b.(a -> b) ex loc -> unit =
                     fun f ->
                       let f = Norm.repr f in
                       match f.elt with
                       | HApp(_,g,a) -> print_app g; fprintf ch "%a,"
                                                             exa a
                       | _           -> fprintf ch "%a⟨" (ex ctxt HO) f
                   in
                   print_app f; fprintf ch "%a⟩" exa a
  | HDef(_,d)   -> output_string ch d.expr_name.elt
  | Func(t,a,b,l) ->
     begin
       match l with
       | NoLz   -> let (l,r) = if Prp F < pr then ("(",")") else ("","") in
                   fprintf ch "%s%a %a %a%s"
                     l (ex ctxt (Prp P)) a arrow t exp b r
       | Lazy   -> fprintf ch "lazy⟨%a⟩" exp b
     end
  | Prod(m)     -> let pelt ch (l,(_,a)) = fprintf ch "%s : %a" l exp a in
                   let elp = if A.is_empty m then " ⋯" else "; ⋯" in
                   fprintf ch "{%a%s}" (print_map pelt "; ") m elp
  | DSum(m)     -> let pelt ch (l,(_,a)) =
                     if is_unit_ty ctxt a then fprintf ch "%s" l
                     else fprintf ch "%s of %a" l exp a
                   in
                   fprintf ch "[%a]" (print_map pelt "; ") m
  | Univ(s,b)   -> let (x,a,ctxt) = bndr_open_in ctxt b in
                   fprintf ch "∀%s:%a, %a" (name_of x)
                     sort s (ex ctxt (Prp F)) a
  | Exis(s,b)   -> let (x,a,ctxt) = bndr_open_in ctxt b in
                   fprintf ch "∃%s:%a, %a" (name_of x)
                     sort s (ex ctxt (Prp F)) a
  | FixM(_,o,b,Nil) -> let (x,a,ctxt) = bndr_open_in ctxt b in
                       fprintf ch "μ%a%s, %a"
                         supo o (name_of x) (ex ctxt (Prp F)) a
  | FixM(s,o,b,l) -> exp ch (apply_args (Pos.none (FixM(s,o,b,Nil))) l)
  | FixN(_,o,b,Nil) -> let (x,a,ctxt) = bndr_open_in ctxt b in
                       fprintf ch "ν%a%s, %a"
                         supo o (name_of x) (ex ctxt (Prp F)) a
  | FixN(s,o,b,l) -> exp ch (apply_args (Pos.none (FixN(s,o,b,Nil))) l)
  | Memb(t,a)   -> begin
                     match is_eq e with
                     | Some(e1,s,e2) -> fprintf ch "%a %s %a" exi e1 s exi e2
                     | None ->
                        let
                          (l,r) = if Prp M <= pr then ("(",")") else ("","")
                        in
                        fprintf ch "%s%a ∈ %a%s" l exi t (ex ctxt (Prp M)) a r
                   end
  | Rest(a,c)   -> begin
                     match is_eq e with
                     | Some(e1,s,e2) -> fprintf ch "%a%s%a" exi e1 s exi e2
                     | None ->
                       let (l,r) = if Prp R <= pr then ("(",")") else ("","")
                       in fprintf ch "(%s%a%s | %a)"
                            l (ex ctxt (Prp R)) a r (rel ctxt) c
                   end
  | Impl(e,a)   -> begin
                     fprintf ch "%a ↪ %a" (rel ctxt) e (ex ctxt (Prp R)) a
                   end
  | LAbs(a,b,l) ->
     begin
       match l with
       | NoLz   -> let (x,t,ctxt) = bndr_open_in ctxt b in
                   begin
                     match a with
                     | None   ->
                        let rec fn ctxt acc t =
                          match (Norm.repr t).elt with
                          | Valu(v) ->
                             begin
                               match (Norm.repr v).elt with
                               | LAbs(None,b,NoLz) ->
                                  let (x,t,ctxt) = bndr_open_in ctxt b in
                                  fn ctxt (x::acc) t
                               | _            -> (acc, t, ctxt)
                             end
                          | _            -> (acc, t, ctxt)
                        in
                        let (ls, t, ctxt) = fn ctxt [x] t in
                        let ls = List.rev ls in
                        let pelt ch x = fprintf ch "%s" (name_of x) in
                        fprintf ch "fun %a {%a}"
                                (print_list pelt " ") ls (ex ctxt (Trm F)) t
                     | Some a -> fprintf ch "fun (%s:%a) {%a}"
                                         (name_of x) exp a (ex ctxt (Trm F)) t
                   end
       | Lazy   -> let (x,t,ctxt) = bndr_open_in ctxt b in
                   fprintf ch "fun {%a}" (ex ctxt (Trm F)) t
     end
  | Cons(c,v)   -> if is_unit v then fprintf ch "%s" c.elt
                   else fprintf ch "%s[%a]" c.elt ext v
  | Reco(m)     -> let pelt ch (l,(_,a)) =
                     fprintf ch "%s = %a" l ext a in
                   fprintf ch "{%a}" (print_map pelt ", ") m
  | Scis        -> output_string ch "✂"
  | VDef(d)     -> output_string ch d.value_name.elt
  | Valu(v)     -> ex ctxt pr ch v
  | Appl(t,u,lz)->
     begin
       let (l,r) = if Trm P < pr then ("(",")") else ("","") in
       match lz with
       | NoLz   -> fprintf ch "%s%a %a%s" l (ex ctxt (Trm P)) t
                     (ex ctxt (Trm A)) u r
       | Lazy   -> fprintf ch "%sforce %a%s" l (ex ctxt (Trm P)) t r
     end
  | MAbs(b)     -> let (x,t,ctxt) = bndr_open_in ctxt b in
                   fprintf ch "save %s {%a}" (name_of x) (ex ctxt (Trm F)) t
  | Name(s,t)   -> fprintf ch "restore %a %a" exa s ext t
  | Proj(v,l)   -> fprintf ch "%a.%s" (ex ctxt (Trm A)) v l.elt
  | Case(v,m)   -> let pelt ch (c, (_, b)) =
                     let (x,t,ctxt) = bndr_open_in ctxt b in
                     fprintf ch "%s[%s] → %a"
                             c (name_of x) (ex ctxt (Trm F)) t
                   in
                   let pcase = print_map pelt " " in
                   fprintf ch "case %a {%a}" ext v pcase m
  | FixY(b)     -> let (x,_,_) = bndr_open_in ctxt b in
                   fprintf ch "%s" (name_of x)
  | Prnt(s)     -> fprintf ch "print(%S)" s
  | Repl(t,u)   -> fprintf ch "check {%a} for {%a}" ext u ext t
  | Delm(t)     -> fprintf ch "delim {%a}" ext t
  | Hint(_,t)   -> ex ctxt pr ch t
  | Conv        -> output_string ch "∞"
  | Succ(o)     -> fprintf ch "%a+1" exo o
  | Coer(_,e,a) -> fprintf ch "(%a : %a)" ext e exp a
  | Such(_,_,r) ->
      output_string ch "let ";
      let rec aux : type a b. (a, prop * b ex loc) bseq -> unit = fun seq ->
        match seq with
        | BLast(s,b) ->
            let (x,(a,t)) = unbind b in
            fprintf ch "%s:%a s.t. " (name_of x) sort s;
            let _ =
              match r.opt_var with
              | SV_None    -> output_string ch "_"
              | SV_Valu(v) -> ext ch v
              | SV_Stac(s) -> exa ch s
            in
            fprintf ch " : %a; %a" exp a ext t
        | BMore(s,b) ->
            let (x,seq) = unbind b in
            fprintf ch "%s:%a, " (name_of x) sort s;
            aux seq
      in aux r.binder
  | Chck(_,_,_,e) -> fprintf ch "%a" ext e (* TODO *)
  | CPsi        -> fprintf ch "ψ"
  | Clck(v)     -> fprintf ch "χ(%a)" exp v
  | ITag(_,i)   -> fprintf ch "#%i" i
  | VWit(w)     -> fprintf ch "%s%a" w.name print_vars e
  | SWit(w)     -> fprintf ch "%s%a" w.name print_vars e
  | UWit(w)     -> fprintf ch "%s%a" w.name print_vars e
  | EWit(w)     -> fprintf ch "%s%a" w.name print_vars e
  | OWMu(w)     -> fprintf ch "%s%a" w.name print_vars e
  | OWNu(w)     -> fprintf ch "%s%a" w.name print_vars e
  | OSch(i,_,w) -> fprintf ch "%s%a" (fst w.name).(i) print_vars e
  | ESch(s,i,w) -> fprintf ch "%s%a" (snd w.name).(i) print_vars e
  | UVar(_,u)   -> fprintf ch "?%i" u.uvar_key
  | Goal(_,s,_) -> fprintf ch "{- %s -}" s
  | VPtr(p)     -> fprintf ch "VPtr(%a)" VPtr.print p
  | TPtr(p)     -> fprintf ch "TPtr(%a)"  Ptr.print p

and rel ctxt ch cnd =
  let eq b = if b then "=" else "≠" in
    match cnd with
    | Equiv(t,b,u) -> fprintf ch "%a %s %a"
                        (ex ctxt (Trm F)) t (eq b)
                        (ex ctxt (Trm F)) u
    | NoBox(v)     -> fprintf ch "%a↓" (ex ctxt (Trm F)) v

let bndr ch b =
  let ctxt = empty_ctxt in
  let (x, t, ctxt) = bndr_open_in ctxt b in
  fprintf ch "%s.%a" (name_of x) (ex ctxt Any) t
let ex ch t = ex empty_ctxt Any ch t
let _ = fprint.f <- ex
let rel ch r = rel empty_ctxt ch r

let print_fix_sch ch sch =
  let (x,t) = unbind (snd (fst sch.fsch_judge)) in
  let (vars,k) = unmbind (snd sch.fsch_judge) in
  let vars = Array.map (fun x -> Pos.none (mk_free O x)) vars in
  let print_vars = print_list ex "," in
  fprintf ch "%a (⊢ λx.Y(λ%s.%a,x) : %a)" print_vars (Array.to_list vars)
    (name_of x) ex t ex k

let print_sub_sch ch sch =
  let (vars,f) = unmbind sch.ssch_judge in
  let rec fn acc = function
    | Cst(a,b) -> (List.rev acc,a,b)
    | Bnd(s,f) -> let (x,f) = unbind f in fn (name_of x :: acc) f
  in
  let (vars2, k1, k2) = fn [] f in
  let vars = Array.map (fun x -> Pos.none (mk_free O x)) vars in
  let print_vars = print_list ex "," in
  let rel = List.map (fun (i,j) -> (vars.(i), vars.(j))) sch.ssch_relat in
  let print_cmp ch (i,j) = fprintf ch "%a<%a" ex i ex j in
  let print_rel = print_list print_cmp "," in
  fprintf ch "%a %a (%a ⊢ %a < %a)" print_vars (Array.to_list vars)
          (print_list output_string " ") vars2 print_rel rel ex k1 ex k2

let print_sch ch sch =
  match sch with
  | FixSch sch -> print_fix_sch ch sch
  | SubSch sch -> print_sub_sch ch sch

let omb ch b =
  let (vars,k) = unmbind b in
  let vars = Array.map (fun x -> Pos.none (mk_free O x)) vars in
  let print_vars = print_list ex "," in
  fprintf ch "%a.%a" print_vars (Array.to_list vars) ex k

let rec get_lambda_name : type a. a ex loc -> string =
  fun e ->
    let e = Norm.whnf e in
    match e.elt with
    | LAbs(_,b,_) -> (bndr_name b).elt
    | VDef(d)     -> get_lambda_name (d.value_eras)
    | HDef(_,d)   -> get_lambda_name (d.expr_def)
    | Valu(v)     -> get_lambda_name v
    | _           -> "x"

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

type pretty =
  | Decl of v ex loc * p ex loc
  | Rela of rel
  | Posi of o ex loc
  | CPrj of v ex loc * string * v ex loc

let pretty ps =
  let fn = function
    | Decl(v,p)    -> Printf.printf "%a : %a\n" ex v ex p
    | Rela(r)      -> Printf.printf "%a\n" rel r
    | Posi (o)     -> Printf.printf "%a > 0\n" ex o
    | CPrj (v,l,w) -> Printf.printf "%a.%s = %a\n" ex v l ex w
  in
  List.iter fn ps
