(** Printing functions for expressions. *)

open Bindlib
open Sorts
open Pos
open Ast
open Output
open Printf

let print_map : (string * 'a) printer -> string -> 'a A.t printer =
  fun pelem sep ch m -> print_list pelem sep ch (A.bindings m)

let is_tuple ls =
  try
    for i = 1 to List.length ls do
      if not (List.mem_assoc (string_of_int i) ls) then raise Exit
    done; true
  with Exit -> false

let rec print_sort : type a. a sort printer = fun ch s ->
  match s with
  | V      -> output_string ch "ι"
  | T      -> output_string ch "τ"
  | S      -> output_string ch "σ"
  | P      -> output_string ch "ο"
  | O      -> output_string ch "κ"
  | F(a,b) -> if match a with F(_,_) -> true | _ -> false then
                fprintf ch "(%a) → %a" print_sort a print_sort b
              else
                fprintf ch "%a → %a" print_sort a print_sort b

let print_full = ref false

let cname : type a. a ex loc -> string = fun e ->
  match e.elt with
  | Vari _ -> "Vari"
  | HFun _ -> "HFun"
  | HApp _ -> "HApp"
  | HDef _ -> "HDef"
  | Func _ -> "Func"
  | Prod _ -> "Prod"
  | DSum _ -> "DSum"
  | Univ _ -> "Univ"
  | Exis _ -> "Exis"
  | FixM _ -> "FixM"
  | FixN _ -> "FixN"
  | Memb _ -> "Memb"
  | Rest _ -> "Rest"
  | Impl _ -> "Impl"
  | LAbs _ -> "LAbs"
  | Cons _ -> "Cons"
  | Reco _ -> "Reco"
  | Scis   -> "Scis"
  | VDef _ -> "VDef"
  | Valu _ -> "Valu"
  | Appl _ -> "Appl"
  | MAbs  _ -> "MAbs "
  | Name _ -> "Name"
  | Proj _ -> "Proj"
  | Case _ -> "Case"
  | FixY _ -> "FixY"
  | Prnt _ -> "Prnt"
  | Epsi   -> "Epsi"
  | Push _ -> "Push"
  | Fram _ -> "Fram"
  | Conv   -> "Conv"
  | Succ _ -> "Succ"
  | OWMu _ -> "OWMu"
  | OWNu _ -> "OWNu"
  | OSch _ -> "OSch"
  | Coer _ -> "Coer"
  | Such _ -> "Such"
  | ITag _ -> "ITag"
  | Dumm   -> "Dumm"
  | VWit _ -> "VWit"
  | SWit _ -> "SWit"
  | UWit _ -> "UWit"
  | EWit _ -> "EWit"
  | UVar _ -> "UVar"
  | Goal _ -> "Goal"

let print_ex : type a. a ex loc printer = fun ch e ->
  let adone = Ahash.create 101 in
  let test_done e =
    if Ahash.mem adone (Obj.repr e) then true
    else (
      Ahash.add adone (Obj.repr e) ();
      false)
  in
  let rec is_arrow a =
    match a.elt with
    | Func(_,_) -> true
    | Univ(_,_) -> true
    | Exis(_,_) -> true
    | FixM(_,_) -> true
    | FixN(_,_) -> true
    | _         -> false
  in
  let is_unit a =
    false
    (* match a.elt with Prod(m) -> A.is_empty m | _ -> false *)
  in
  let rec print_ex : type a. a ex loc printer = fun ch e ->
    let e = Norm.repr e in
    if test_done e && !print_full then output_string ch "..." else
    match e.elt with
    | Vari(_,x)   -> output_string ch (name_of x)
    | HFun(s,_,b) -> let (x,t) = unbind (mk_free s) (snd b) in
                     fprintf ch "(%s ↦ %a)" (name_of x) print_ex t
    | HApp(_,f,a) -> let rec print_app : type a b.(a -> b) ex loc -> unit =
                       fun f ->
                         let f = Norm.repr f in
                         match f.elt with
                         | HApp(_,g,a) -> print_app g; fprintf ch "%a,"
                                                               print_ex a
                         | _           -> fprintf ch "%a<" print_ex f
                     in
                     print_app f; fprintf ch "%a>" print_ex a
    | HDef(_,d)   -> output_string ch d.expr_name.elt
    | Func(a,b)   -> let (l,r) = if is_arrow a then ("(",")") else ("","") in
                     fprintf ch "%s%a%s ⇒ %a" l print_ex a r print_ex b
    | Prod(m)     -> let pelt ch (l,(_,a)) =
                       fprintf ch "%s : %a" l print_ex a
                     in fprintf ch "{%a}" (print_map pelt "; ") m
    | DSum(m)     -> let pelt ch (l,(_,a)) =
                       fprintf ch "%s : %a" l print_ex a
                     in fprintf ch "[%a]" (print_map pelt "; ") m
    | Univ(s,b)   -> let (x,a) = unbind (mk_free s) (snd b) in
                     fprintf ch "∀%s:%a.%a" (name_of x)
                       print_sort s print_ex a
    | Exis(s,b)   -> let (x,a) = unbind (mk_free s) (snd b) in
                     fprintf ch "∃%s:%a.%a" (name_of x)
                       print_sort s print_ex a
    | FixM(o,b)   -> let (x,a) = unbind (mk_free P) (snd b) in
                     fprintf ch "μ(%a) %s.%a"
                             print_ex o (name_of x) print_ex a
    | FixN(o,b)   -> let (x,a) = unbind (mk_free P) (snd b) in
                     fprintf ch "ν(%a) %s.%a"
                             print_ex o (name_of x) print_ex a
    | Memb(t,a)   -> let (l,r) = if is_arrow a then ("(",")") else ("","") in
                     fprintf ch "%a ∈ %s%a%s" print_ex t l print_ex a r
    | Rest(a,e)   -> if is_unit a then print_cond ch e else
                       let (l,r) = if is_arrow a then ("(",")") else ("","") in
                       fprintf ch "(%s%a%s | %a)" l print_ex a r print_cond e
    | Impl(e,a)   -> fprintf ch "%a ↪ %a" print_cond e print_ex a
    | LAbs(ao,b)  -> let (x,t) = unbind (mk_free V) (snd b) in
                     begin
                       match ao with
                       | None   -> fprintf ch "λ%s.%a"
                                           (name_of x) print_ex t
                       | Some a -> fprintf ch "λ(%s:%a).%a"
                                           (name_of x) print_ex a print_ex t
                     end
    | Cons(c,v)   -> fprintf ch "%s[%a]" c.elt print_ex v
    | Reco(m)     -> let pelt ch (l,(_,a)) =
                       fprintf ch "%s = %a" l print_ex a
                     in fprintf ch "{%a}" (print_map pelt "; ") m
    | Scis        -> output_string ch "✂"
    | VDef(d)     -> output_string ch d.value_name.elt
    | Valu(v)     -> if !print_full then output_string ch "↑";
                     print_ex ch v
    | Appl(t,u)   -> fprintf ch "(%a) (%a)" print_ex t print_ex u
    | MAbs(b)     -> let (x,t) = unbind (mk_free S) (snd b) in
                     fprintf ch "μ%s.%a" (name_of x) print_ex t
    | Name(s,t)   -> fprintf ch "[%a]%a" print_ex s print_ex t
    | Proj(v,l)   -> fprintf ch "%a.%s" print_ex v l.elt
    | Case(v,m)   -> let pelt ch (c, (_, (_,b))) =
                       let (x,t) = unbind (mk_free V) b in
                       fprintf ch "%s[%s] → %a"
                               c (name_of x) print_ex t
                     in
                     let pcase = print_map pelt " | " in
                     fprintf ch "[%a | %a]" print_ex v pcase m
    | FixY(f,v)   -> let (x,t) = unbind (mk_free V) (snd f) in
                     fprintf ch "Y(λ%s.%a, %a)" (name_of x)
                       print_ex t print_ex v
    | Prnt(s)     -> fprintf ch "print(%S)" s
    | Epsi        -> output_string ch "ε"
    | Push(v,s)   -> fprintf ch "%a · %a" print_ex v print_ex s
    | Fram(t,s)   -> fprintf ch "[%a] %a" print_ex t print_ex s
    | Conv        -> output_string ch "∞"
    | Succ(o)     -> fprintf ch "%a+1" print_ex o
    | Coer(_,e,a) -> fprintf ch "(%a : %a)" print_ex e print_ex a
    | Such(_,_,_) -> assert false (* FIXME #58 *)
    | ITag(_,i)   -> fprintf ch "#%i" i
    | Dumm        -> output_string ch "∅"
    (* TODO #53 give a number to all witnesses to distinguish equal ones even
     when print_full is false *)
    | VWit(f,a,b) -> if !print_full then
                       let (x,t) = unbind (mk_free V) (snd f) in
                       fprintf ch "ει(%s|%a∈%a∉%a)" (name_of x)
                               print_ex t print_ex a print_ex b
                     else fprintf ch "ει%s" (bndr_name f).elt
    | SWit(f,b)   -> if !print_full then
                       let (a,t) = unbind (mk_free S) (snd f) in
                       fprintf ch "εσ(%s|%a∉%a)" (name_of a)
                               print_ex t print_ex b
                     else fprintf ch "εσ%s" (bndr_name f).elt
    | UWit(s,t,f) -> if !print_full then
                       let (x,a) = unbind (mk_free s) (snd f) in
                       fprintf ch "ε∀(%s:%a|%a∉%a)" (name_of x)
                               print_sort s print_ex t print_ex a
                     else fprintf ch "ε∀%s" (bndr_name f).elt
    | EWit(s,t,f) -> if !print_full then
                       let (x,a) = unbind (mk_free s) (snd f) in
                       fprintf ch "ε∃(%s:%a|%a∈%a)" (name_of x)
                               print_sort s print_ex t print_ex a
                     else fprintf ch "ε∃%s" (bndr_name f).elt
    | OWMu(o,t,b) -> if !print_full then
                       let (x,a) = unbind (mk_free O) (snd b) in
                       fprintf ch "εκ%s(<%a,%a∈%a)" (name_of x) print_ex o
                         print_ex t print_ex a
                     else fprintf ch "εκμ%s" (bndr_name b).elt
    | OWNu(o,t,b) -> if !print_full then
                       let (x,a) = unbind (mk_free O) (snd b) in
                       fprintf ch "εκ%s(<%a,%a∉%a)" (name_of x) print_ex o
                         print_ex t print_ex a
                     else fprintf ch "εκν%s" (bndr_name b).elt
    | OSch(Some o,i,s) -> if !print_full then
                       fprintf ch "εκ%d(<%a,%a)" i print_ex o print_sch s
                     else fprintf ch "εκ%d(<%a)" i print_ex o
    | OSch(None,i,s) -> if !print_full then
                       fprintf ch "εκ%d(%a)" i print_sch s
                     else fprintf ch "εκ%d" i
    | UVar(_,uv)  -> fprintf ch "?%i" uv.uvar_key
    | Goal(_,str) -> fprintf ch "{- %s -}" str

  and print_cond ch = function
    | Equiv(t,b,u) -> let sym = if b then "=" else "≠" in
                      fprintf ch "%a %s %a" print_ex t sym print_ex u
    | NoBox(v)     -> fprintf ch "%a↓" print_ex v
    | Posit(o)     -> print_ex ch o

  and print_fix_sch ch sch =
    let (x,t) = unbind (mk_free V) (snd (fst sch.fsch_judge)) in
    let (vars,k) = unmbind (mk_free O) (snd sch.fsch_judge) in
    let vars = Array.map (fun x -> Pos.none (free_of x)) vars in
    let print_vars = print_list print_ex "," in
    fprintf ch "%a ( ⊢ λx.Y(λ%s.%a,x) : %a)" print_vars (Array.to_list vars)
            (name_of x) print_ex t print_ex k

  and print_sub_sch ch sch =
    let (vars,(k1,k2)) = unmbind (mk_free O) sch.ssch_judge in
    let vars = Array.map (fun x -> Pos.none (free_of x)) vars in
    let print_vars = print_list print_ex "," in
    let rel = List.map (fun (i,j) -> (vars.(i), vars.(j))) sch.ssch_relat in
    let print_cmp ch (i,j) = fprintf ch "%a<%a" print_ex i print_ex j in
    let print_rel = print_list print_cmp "," in
    fprintf ch "%a (%a ⊢ %a < %a)" print_vars (Array.to_list vars)
            print_rel rel print_ex k1 print_ex k2

 and print_sch ch = function
   | FixSch sch -> print_fix_sch ch sch
   | SubSch sch -> print_sub_sch ch sch

 in print_ex ch e

(* Short names for printing functions. *)
let sort = print_sort
let ex   = print_ex
let omb ch b =
  let (vars,k) = unmbind (mk_free O) b in
  let vars = Array.map (fun x -> Pos.none (free_of x)) vars in
  let print_vars = print_list print_ex "," in
  fprintf ch "%a.%a" print_vars (Array.to_list vars) print_ex k


let full_ex ch e =
  let save = !print_full in
  print_full := true;
  print_ex ch e;
  print_full := save
