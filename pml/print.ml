open Bindlib
open Sorts
open Pos
open Ast

type 'a printer = out_channel -> 'a -> unit

let print_list : 'a printer -> string -> 'a list printer =
  fun pelem sep ch l ->
    let rec prnt ch = function
      | []    -> ()
      | [e]   -> pelem ch e
      | e::es -> pelem ch e; output_string ch sep; prnt ch es
    in prnt ch l

let print_map : (string * 'a) printer -> string -> 'a M.t printer =
  fun pelem sep ch m -> print_list pelem sep ch (M.bindings m)

let is_tuple ls =
  try
    for i = 1 to List.length ls do
      if not (List.mem_assoc (string_of_int i) ls) then raise Exit
    done; true
  with Exit -> false

let rec print_sort : type a. out_channel -> a sort -> unit = fun ch s ->
  match s with
  | V      -> output_string ch "ι"
  | T      -> output_string ch "τ"
  | S      -> output_string ch "σ"
  | P      -> output_string ch "ο"
  | O      -> output_string ch "κ"
  | F(a,b) -> let isfun = match a with F(_,_) -> true | _ -> false in
              if isfun then
                Printf.fprintf ch "(%a) → %a" print_sort a print_sort b
              else
                Printf.fprintf ch "%a → %a" print_sort a print_sort b

let rec print_ex : type a. out_channel -> a ex loc -> unit =
  fun ch e ->
    let e = Norm.whnf e in
    match e.elt with
    | Vari(x)     -> output_string ch (name_of x)
    | HFun(b)     -> let (x,t) = unbind mk_free (snd b) in
                     Printf.fprintf ch "(%s ↦ %a)" (name_of x) print_ex t
    | HApp(_,f,a) -> Printf.fprintf ch "%a(%a)" print_ex f print_ex a
    | Func(a,b)   -> Printf.fprintf ch "%a ⇒ %a" print_ex a print_ex b
    | Prod(m)     -> let pelt ch (l,(_,a)) =
                       Printf.fprintf ch "%s : %a" l print_ex a
                     in Printf.fprintf ch "{%a}" (print_map pelt "; ") m
    | DSum(m)     -> let pelt ch (l,(_,a)) =
                       Printf.fprintf ch "%s : %a" l print_ex a
                     in Printf.fprintf ch "[%a]" (print_map pelt "; ") m
    | Univ(_,b)   -> let (x,a) = unbind mk_free (snd b) in
                     Printf.fprintf ch "∀%s.%a" (name_of x) print_ex a
    | Exis(_,b)   -> let (x,a) = unbind mk_free (snd b) in
                     Printf.fprintf ch "∃%s.%a" (name_of x) print_ex a
    | FixM(o,b)   -> let (x,a) = unbind mk_free (snd b) in
                     Printf.fprintf ch "μ(%a) %s.%a"
                       print_ex o (name_of x) print_ex a
    | FixN(o,b)   -> let (x,a) = unbind mk_free (snd b) in
                     Printf.fprintf ch "ν(%a) %s.%a"
                       print_ex o (name_of x) print_ex a
    | Memb(t,a)   -> Printf.fprintf ch "%a ∈ %a" print_ex t print_ex a
    | Rest(a,e)   -> let print_eq ch (t,b,u) =
                       let sym = if b then "=" else "≠" in
                       Printf.fprintf ch "%a %s %a" print_ex t sym print_ex u
                     in Printf.fprintf ch "%a | %a" print_ex a print_eq e
    | LAbs(ao,b)  -> let (x,t) = unbind mk_free (snd b) in
                     Printf.fprintf ch "λ%s.%a" (name_of x) print_ex t
                     (* TODO print ao *)
    | Cons(c,v)   -> Printf.fprintf ch "%s[%a]" c.elt print_ex v
    | Reco(m)     -> let pelt ch (l,(_,a)) =
                       Printf.fprintf ch "%s = %a" l print_ex a
                     in Printf.fprintf ch "{%a}" (print_map pelt "; ") m
    | Scis        -> output_string ch "✂"
    | Valu(v)     -> print_ex ch v
    | Appl(t,u)   -> Printf.fprintf ch "(%a) %a" print_ex t print_ex u
    | MAbs(ao,b)  -> let (x,t) = unbind mk_free (snd b) in
                     Printf.fprintf ch "μ%s.%a" (name_of x) print_ex t
                     (* TODO print ao *)
    | Name(s,t)   -> Printf.fprintf ch "[%a]%a" print_ex s print_ex t
    | Proj(v,l)   -> Printf.fprintf ch "%a.%s" print_ex v l.elt
    | Case(v,m)   -> let pelt ch (c, (_, (_,b))) =
                       let (x,t) = unbind mk_free b in
                       Printf.fprintf ch "%s[%s] → %a"
                         c (name_of x) print_ex t
                     in
                     let pcase = print_map pelt " | " in
                     Printf.fprintf ch "[%a | %a]" print_ex v pcase m
    | FixY(t,v)   -> Printf.fprintf ch "Y(%a, %a)" print_ex t print_ex v
    | Epsi        -> output_string ch "ε"
    | Push(v,s)   -> Printf.fprintf ch "%a · %a" print_ex v print_ex s
    | Fram(t,s)   -> Printf.fprintf ch "[%a] %a" print_ex t print_ex s
    | Conv        -> output_string ch "∞"
    | Succ(o)     -> Printf.fprintf ch "%a+1" print_ex o
    | DPrj(t,x)   -> Printf.fprintf ch "(%a).%s" print_ex t x.elt
    | VTyp(v,a)   -> Printf.fprintf ch "(%a : %a)" print_ex v print_ex a
    | TTyp(t,a)   -> Printf.fprintf ch "(%a : %a)" print_ex t print_ex a
    | VLam(_,b)   -> let (x,t) = unbind mk_free (snd b) in
                     Printf.fprintf ch "Λ%s.%a" (name_of x) print_ex t
    | TLam(_,b)   -> let (x,t) = unbind mk_free (snd b) in
                     Printf.fprintf ch "Λ%s.%a" (name_of x) print_ex t
    | ITag(i)     -> Printf.fprintf ch "#%i" i
    | Dumm        -> output_string ch "∅"
    | VWit(_,_,_) -> output_string ch "ει"
    | SWit(_,_)   -> output_string ch "εσ"
    | UWit(_,_,_) -> output_string ch "ε∀"
    | EWit(_,_,_) -> output_string ch "ε∃"
    | UVar(i,_,_) -> Printf.fprintf ch "?%i" i
