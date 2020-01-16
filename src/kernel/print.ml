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
              | true , false -> fprintf ch "→"
              | false, true  -> fprintf ch "⇏"
              | true , true  -> fprintf ch "↛")
  | _        -> fprintf ch "?>"

let removeq : ('a -> 'a -> bool) -> 'a list ref -> 'a -> bool = fun eq ls x ->
  let rec fn acc = function
    | [] -> false
    | y::l -> if eq x y then (ls := List.rev_append acc l; true)
              else fn (y::acc) l
  in
  fn [] !ls

let collect_exis : type s a.s sort -> a ex loc -> s var list * a ex loc =
  fun s e ->
  let rec fn : type a.s var list -> a ex loc -> s var list * a ex loc =
    fun acc e ->
      let e = Norm.repr e in
      match e.elt with
      | Exis(s', f) ->
         begin
           match eq_sort s s' with
           | Eq.Eq  ->  let ((x:s var), t) = bndr_open f in
                        fn (x::acc) t
           | Eq.NEq -> (acc, e)
         end
      | _           -> (acc, e)
  in
  fn [] e

type _ sugar =
  | NoSugar : 'a sugar
  | StrictReco : (pos option * prop) Assoc.t -> p sugar
  | Tuple      : valu list -> v sugar
  | TupleType  : prop list -> p sugar
  | DepSum     : t var list * prop * prop -> p sugar
  | Compr      : t var * prop * rel -> p sugar
  | Def        : 'a ex loc -> 'a sugar

let is_comprehension : type a. a ex loc -> a sugar = fun e ->
  match (Norm.repr e).elt with
  | Exis(T, f) ->
     begin
       let (x, t) = bndr_open f in
       match (Norm.repr t).elt with
       | Memb(t,p) ->
          begin
            match ((Norm.repr t).elt, (Norm.repr p).elt) with
            | (Vari(_,y), Rest(p,eq)) when eq_vars x y -> Compr(x,p,eq)
            | _                                        -> NoSugar
          end
       | _         -> NoSugar
     end
  | _          -> NoSugar

let is_strict_record : type a. a ex loc -> a sugar =
  fun e ->
  let (ls, e) = collect_exis V e in
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
               then StrictReco m2
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
  if is_def e then NoSugar else
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

let is_dep_sum : type a.a ex loc -> a sugar = fun e ->
  let (ls, e) = collect_exis T e in
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
         DepSum(vars, ty, List.nth ps (List.length ls))
       with
         Exit -> NoSugar
     else NoSugar
  | _ -> assert false

let is_sugar : type a.a ex loc -> a sugar = fun e ->
  let s = is_strict_record e in
  if s <> NoSugar then s else
  let s = is_tuple e in
  if s <> NoSugar then s else
  let s = is_dep_sum e in
  if s <> NoSugar then s else
  let s = is_comprehension e in
  if s <> NoSugar then s else
  let s = is_def e in
  if s <> NoSugar then s else
  s

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
  let supo ch o = match (Norm.repr o).elt with
    | Conv -> ()
    | _    -> fprintf ch "^%a " exo o
  in
  match is_sugar e with
  | StrictReco m  -> let pelt ch (l,(_,a)) =
                       fprintf ch "%s : %a" l exp a
                     in fprintf ch "{%a}" (print_map pelt "; ") m
  | Tuple ls      -> fprintf ch "(%a)" (print_list ext ", ") ls
  | TupleType ls  -> let (l,r) = if Prp P < pr then ("(",")") else ("","") in
                     fprintf ch "%s%a%s" l
                       (print_list (ex (Prp R)) " × ") ls r
  | DepSum(l,a,p) -> let pelt ch x = fprintf ch "%s" (name_of x) in
                     fprintf ch "∃%a∈%a, %a"
                       (print_list pelt " ") l exp a exp p
  | Compr(x,p,r)  -> fprintf ch "{ %s ∈ %a | %a }" (name_of x) exp p rel r
  | Def e         -> ex pr ch e
  | NoSugar       ->
  match e.elt with
  | Vari(_,x)   -> output_string ch (name_of x)
  | HFun(s,_,b) -> let (x,t) = bndr_open b in
                   fprintf ch "(%s ↦ %a)" (name_of x) exa t
  | HApp(_,f,a) -> let rec print_app : type a b.(a -> b) ex loc -> unit =
                     fun f ->
                       let f = Norm.repr f in
                       match f.elt with
                       | HApp(_,g,a) -> print_app g; fprintf ch "%a,"
                                                             exa a
                       | _           -> fprintf ch "%a⟨" (ex HO) f
                   in
                   print_app f; fprintf ch "%a⟩" exa a
  | HDef(_,d)   -> output_string ch d.expr_name.elt
  | Func(t,a,b,l) ->
     begin
       match l with
       | NoLz   -> let (l,r) = if Prp F < pr then ("(",")") else ("","") in
                   fprintf ch "%s%a %a %a%s" l (ex (Prp P)) a arrow t exp b r
       | Lazy   -> fprintf ch "lazy⟨%a⟩" exp b
     end
  | Prod(m)     -> let pelt ch (l,(_,a)) = fprintf ch "%s : %a" l exp a in
                   let elp = if A.is_empty m then " ⋯" else "; ⋯" in
                   fprintf ch "{%a%s}" (print_map pelt "; ") m elp
  | DSum(m)     -> let pelt ch (l,(_,a)) = fprintf ch "%s : %a" l exp a in
                   fprintf ch "[%a]" (print_map pelt "; ") m
  | Univ(s,b)   -> let (x,a) = bndr_open b in
                   fprintf ch "∀%s:%a, %a" (name_of x)
                     sort s exp a
  | Exis(s,b)   -> let (x,a) = bndr_open b in
                   fprintf ch "∃%s:%a, %a" (name_of x)
                     sort s exp a
  | FixM(_,o,b,Nil) -> let (x,a) = bndr_open b in
                   fprintf ch "μ%a%s, %a" supo o (name_of x) exp a
  | FixM(s,o,b,l) -> exp ch (apply_args (Pos.none (FixM(s,o,b,Nil))) l)
  | FixN(_,o,b,Nil) -> let (x,a) = bndr_open b in
                   fprintf ch "ν%a%s, %a" supo o (name_of x) exp a
  | FixN(s,o,b,l) -> exp ch (apply_args (Pos.none (FixN(s,o,b,Nil))) l)
  | Memb(t,a)   -> begin
                     match is_eq e with
                     | Some(e1,s,e2) -> fprintf ch "%a%s%a" exi e1 s exi e2
                     | None ->
                       let (l,r) = if Prp M <= pr then ("(",")") else ("","")
                       in fprintf ch "%s%a ∈ %a%s" l exi t (ex (Prp M)) a r
                   end
  | Rest(a,c)   -> begin
                     match is_eq e with
                     | Some(e1,s,e2) -> fprintf ch "%a%s%a" exi e1 s exi e2
                     | None ->
                       let (l,r) = if Prp R <= pr then ("(",")") else ("","")
                       in fprintf ch "(%s%a%s | %a)" l (ex (Prp R)) a r rel c
                   end
  | Impl(e,a)   -> begin
                     fprintf ch "%a ↪ %a" rel e (ex (Prp R)) a
                   end
  | LAbs(a,b,l) ->
     begin
       match l with
       | NoLz   -> let (x,t) = bndr_open b in
                   begin
                     match a with
                     | None   ->
                        let rec fn acc t =
                          match (Norm.repr t).elt with
                          | Valu(v) ->
                             begin
                               match (Norm.repr v).elt with
                               | LAbs(None,b,NoLz) ->
                                  let (x,t) = bndr_open b in
                                  fn (x::acc) t
                               | _            -> (acc, t)
                             end
                          | _            -> (acc, t)
                        in
                        let (ls, t) = fn [x] t in
                        let ls = List.rev ls in
                        let pelt ch x = fprintf ch "%s" (name_of x) in
                        fprintf ch "fun %a {%a}"
                                (print_list pelt " ") ls ext t
                     | Some a -> fprintf ch "fun (%s:%a) {%a}"
                                         (name_of x) exp a ext t
                   end
       | Lazy   -> let (x,t) = bndr_open b in
                   fprintf ch "fun {%a}" ext t
     end
  | Cons(c,v)   -> if is_unit v then fprintf ch "%s" c.elt
                   else fprintf ch "%s[%a]" c.elt ext v
  | Reco(m)     -> let pelt ch (l,(_,a)) =
                     fprintf ch "%s = %a" l ext a in
                   fprintf ch "{%a}" (print_map pelt "; ") m
  | Scis        -> output_string ch "✂"
  | VDef(d)     -> output_string ch d.value_name.elt
  | Valu(v)     -> ex pr ch v
  | Appl(t,u,lz)->
     begin
       let (l,r) = if Trm P < pr then ("(",")") else ("","") in
       match lz with
       | NoLz   -> fprintf ch "%s%a %a%s" l (ex (Trm P)) t (ex (Trm A)) u r
       | Lazy   -> fprintf ch "%sforce %a%s" l (ex (Trm P)) t r
     end
  | MAbs(b)     -> let (x,t) = bndr_open b in
                   fprintf ch "save %s {%a}" (name_of x) ext t
  | Name(s,t)   -> fprintf ch "restore %a %a" exa s ext t
  | Proj(v,l)   -> fprintf ch "%a.%s" (ex (Trm A)) v l.elt
  | Case(v,m)   -> let pelt ch (c, (_, b)) =
                     let (x,t) = bndr_open b in
                     fprintf ch "%s[%s] → %a"
                             c (name_of x) ext t
                   in
                   let pcase = print_map pelt " " in
                   fprintf ch "case %a {%a}" ext v pcase m
  | FixY(b)     -> let (x,t) = bndr_open b in
                   fprintf ch "fix %s {%a}" (name_of x) ext t
  | Prnt(s)     -> fprintf ch "print(%S)" s
  | Repl(t,u)   -> fprintf ch "check {%a} for {%a}" ext t ext u
  | Delm(t)     -> fprintf ch "delim {%a}" ext t
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
  | PSet(l,s,e) -> fprintf ch "%a; %a" print_set_param l ext e
  | ITag(_,i)   -> fprintf ch "#%i" i
  | VWit(w)     -> fprintf ch "%s%a" w.name print_vars e
  | SWit(w)     -> fprintf ch "%s%a" w.name print_vars e
  | UWit(w)     -> fprintf ch "%s%a" w.name print_vars e
  | EWit(w)     -> fprintf ch "%s%a" w.name print_vars e
  | OWMu(w)     -> fprintf ch "%s%a" w.name print_vars e
  | OWNu(w)     -> fprintf ch "%s%a" w.name print_vars e
  | OSch(i,_,w) -> fprintf ch "%s%a" w.name.(i) print_vars e
  | ESch(s,i,w) -> fprintf ch "%a??" print_vars e
  | UVar(_,u)   -> fprintf ch "?%i" u.uvar_key
  | Goal(_,s)   -> fprintf ch "{- %s -}" s
  | VPtr(p)     -> fprintf ch "VPtr(%a)" VPtr.print p
  | TPtr(p)     -> fprintf ch "TPtr(%a)"  Ptr.print p

and print_set_param ch = function
  | Alvl(b,d)   -> fprintf ch "auto %d %d" b d
  | Logs(s)     -> fprintf ch "log %s" s
  | Keep(b)     -> fprintf ch "keep_intermediate %b" b
and rel ch cnd =
  let eq b = if b then "=" else "≠" in
    match cnd with
    | Equiv(t,b,u) -> fprintf ch "%a %s %a"
                              (ex (Trm F)) t (eq b) (ex (Trm F)) u
    | NoBox(v)     -> fprintf ch "%a↓" (ex (Trm F)) v

let ex ch t = ex Any ch t

let bndr ch b =
  let (x, t) = bndr_open b in
  fprintf ch "%s.%a" (name_of x) ex t

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
