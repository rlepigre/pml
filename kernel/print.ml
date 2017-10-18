(** Printing functions for expressions. *)

open Bindlib
open Sorts
open Pos
open Ast
open Output
open Printf
open Uvars

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
              fprintf ch "%s%a%s → %a" l sort a r sort b

let print_vars ch e =
  let vars = uvars e in
  match vars with
  | [] -> ()
  | U (_,x)::l -> fprintf ch "(?%d%t)" x.uvar_key
                    (fun ch -> List.iter (function U (_,x) ->
                                   fprintf ch ",?%d" x.uvar_key) l)

let rec ex : type a. a ex loc printer = fun ch e ->
  let rec is_arrow : type a. a ex loc -> bool = fun e ->
    match (Norm.repr e).elt with
    | Func(_,_) -> true
    | Univ(_,_) -> true
    | Exis(_,_) -> true
    | FixM(_,_) -> true
    | FixN(_,_) -> true
    | _         -> false
  in
  let e = Norm.repr e in
  match e.elt with
  | Vari(_,x)   -> output_string ch (name_of x)
  | HFun(s,_,b) -> let (x,t) = unbind (mk_free s) (snd b) in
                   fprintf ch "(%s ↦ %a)" (name_of x) ex t
  | HApp(_,f,a) -> let rec print_app : type a b.(a -> b) ex loc -> unit =
                     fun f ->
                       let f = Norm.repr f in
                       match f.elt with
                       | HApp(_,g,a) -> print_app g; fprintf ch "%a,"
                                                             ex a
                       | _           -> fprintf ch "%a<" ex f
                   in
                   print_app f; fprintf ch "%a>" ex a
  | HDef(_,d)   -> output_string ch d.expr_name.elt
  | Func(a,b)   -> let (l,r) = if is_arrow a then ("(",")") else ("","") in
                   fprintf ch "%s%a%s ⇒ %a" l ex a r ex b
  | Prod(m)     -> let pelt ch (l,(_,a)) =
                     fprintf ch "%s : %a" l ex a
                   in fprintf ch "{%a}" (print_map pelt "; ") m
  | DSum(m)     -> let pelt ch (l,(_,a)) =
                     fprintf ch "%s : %a" l ex a
                   in fprintf ch "[%a]" (print_map pelt "; ") m
  | Univ(s,b)   -> let (x,a) = unbind (mk_free s) (snd b) in
                   fprintf ch "∀%s:%a.%a" (name_of x)
                     sort s ex a
  | Exis(s,b)   -> let (x,a) = unbind (mk_free s) (snd b) in
                   fprintf ch "∃%s:%a.%a" (name_of x)
                     sort s ex a
  | FixM(o,b)   -> let (x,a) = unbind (mk_free P) (snd b) in
                   fprintf ch "μ(%a) %s.%a"
                           ex o (name_of x) ex a
  | FixN(o,b)   -> let (x,a) = unbind (mk_free P) (snd b) in
                   fprintf ch "ν(%a) %s.%a"
                           ex o (name_of x) ex a
  | Memb(t,a)   -> let (l,r) = if is_arrow a then ("(",")") else ("","") in
                   fprintf ch "%a ∈ %s%a%s" ex t l ex a r
  | Rest(a,e)   -> let (l,r) = if is_arrow a then ("(",")") else ("","") in
                   fprintf ch "(%s%a%s | %a)" l ex a r rel e
  | Impl(e,a)   -> fprintf ch "%a ↪ %a" rel e ex a
  | LAbs(ao,b)  -> let (x,t) = unbind (mk_free V) (snd b) in
                   begin
                     match ao with
                     | None   -> fprintf ch "λ%s.%a"
                                         (name_of x) ex t
                     | Some a -> fprintf ch "λ(%s:%a).%a"
                                         (name_of x) ex a ex t
                   end
  | Cons(c,v)   -> fprintf ch "%s[%a]" c.elt ex v
  | Reco(m)     -> let pelt ch (l,(_,a)) =
                     fprintf ch "%s = %a" l ex a
                   in fprintf ch "{%a}" (print_map pelt "; ") m
  | Scis        -> output_string ch "✂"
  | VDef(d)     -> output_string ch d.value_name.elt
  | Valu(v)     -> ex ch v
  | Appl(t,u)   -> fprintf ch "(%a) (%a)" ex t ex u
  | MAbs(b)     -> let (x,t) = unbind (mk_free S) (snd b) in
                   fprintf ch "μ%s.%a" (name_of x) ex t
  | Name(s,t)   -> fprintf ch "[%a]%a" ex s ex t
  | Proj(v,l)   -> fprintf ch "%a.%s" ex v l.elt
  | Case(v,m)   -> let pelt ch (c, (_, (_,b))) =
                     let (x,t) = unbind (mk_free V) b in
                     fprintf ch "%s[%s] → %a"
                             c (name_of x) ex t
                   in
                   let pcase = print_map pelt " | " in
                   fprintf ch "[%a | %a]" ex v pcase m
  | FixY(f,v)   -> let (x,t) = unbind (mk_free V) (snd f) in
                   fprintf ch "Y(λ%s.%a, %a)" (name_of x)
                     ex t ex v
  | Prnt(s)     -> fprintf ch "print(%S)" s
  | Epsi        -> output_string ch "ε"
  | Push(v,s)   -> fprintf ch "%a · %a" ex v ex s
  | Fram(t,s)   -> fprintf ch "[%a] %a" ex t ex s
  | Conv        -> output_string ch "∞"
  | Succ(o)     -> fprintf ch "%a+1" ex o
  | Coer(_,e,a) -> fprintf ch "(%a : %a)" ex e ex a
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
              | SV_Valu(v) -> ex ch v
              | SV_Stac(s) -> ex ch s
            in
            fprintf ch " : %a in %a" ex a ex t
        | BMore(s,b) ->
            let (x,seq) = unbind (mk_free s) b in
            fprintf ch "%s:%a, " (name_of x) sort s;
            aux seq
      in aux r.binder
  | ITag(_,i)   -> fprintf ch "#%i" i
  | Dumm        -> output_string ch "∅"
  | VWit(w)     -> fprintf ch "ει%i%a" !(w.hash) print_vars e
  | SWit(i,_)   -> fprintf ch "εσ%i%a" i print_vars e
  | UWit(i,s,_) -> fprintf ch "ε∀%a%i%a" sort s i print_vars e
  | EWit(i,s,_) -> fprintf ch "ε∃%a%i%a" sort s i print_vars e
  | OWMu(i,_)   -> fprintf ch "εκμ%i%a" i print_vars e
  | OWNu(i,_)   -> fprintf ch "εκν%i%a" i print_vars e
  | OSch(i,_)   -> fprintf ch "εκ%i%a" i print_vars e
  | UVar(_,u)   -> fprintf ch "?%i" u.uvar_key
  | Goal(_,s)   -> fprintf ch "{- %s -}" s
  | VPtr(p)     -> fprintf ch "VPtr(%a)" VPtr.print p
  | TPtr(p)     -> fprintf ch "VPtr(%a)" TPtr.print p

and rel ch cnd =
  let eq b = if b then "=" else "≠" in
    match cnd with
    | Equiv(t,b,u) -> fprintf ch "%a %s %a" ex t (eq b) ex u
    | NoBox(v)     -> fprintf ch "%a↓" ex v
    | Posit(o)     -> ex ch o

let print_fix_sch ch sch =
  let (x,t) = unbind (mk_free V) (snd (fst sch.fsch_judge)) in
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
