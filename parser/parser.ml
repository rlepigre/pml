open Blank
open Tokens

type sort = V | T | S | P | O | Fun of sort * sort | Var of string

let is_fun : sort -> bool = function
  | Fun(_,_) -> true
  | _        -> false

let print_sort ch s =
  let rec psort ch = function
    | V           -> output_string ch "ι"
    | T           -> output_string ch "τ"
    | S           -> output_string ch "σ"
    | P           -> output_string ch "ο"
    | O           -> output_string ch "κ"
    | Var(id)     -> output_string ch id
    | Fun(s1, s2) ->
        if is_fun s1 then Printf.fprintf ch "(%a) → %a" psort s1 psort s2
        else Printf.fprintf ch "%a → %a" psort s1 psort s2
  in psort ch s

let parser ident = ''[a-z]+''
let parser arrow = "→" | "->"

let parser sort (p : [`Atm | `Fun]) =
  | {"ι" | "<iota>"    | "<value>"  }     when p = `Atm -> V
  | {"τ" | "<tau>"     | "<term>"   }     when p = `Atm -> T
  | {"σ" | "<sigma>"   | "<stack>"  }     when p = `Atm -> S
  | {"ο" | "<omicron>" | "<prop>"   }     when p = `Atm -> P
  | {"κ" | "<kappa>"   | "<ordinal>"}     when p = `Atm -> O
  | id:ident                              when p = `Atm -> Var(id)
  | "(" s:(sort `Fun) ")"                 when p = `Atm -> s
  | s1:(sort `Atm) _:arrow s2:(sort `Fun) when p = `Fun -> Fun(s1,s2)
  | s:(sort `Atm)                         when p = `Fun -> s

let sort = sort `Fun

let parser toplevel = "sort" id:ident '=' s:sort
