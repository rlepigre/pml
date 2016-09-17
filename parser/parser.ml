#define LOCATE locate

open Pos
open Blank
open Raw.Sort

let parser ident = ''[a-z]+''
let parser arrow = "→" | "->"

let parser sort (p : [`A | `F]) =
  | {"ι" | "<iota>"    | "<value>"  } when p = `A -> in_pos _loc V
  | {"τ" | "<tau>"     | "<term>"   } when p = `A -> in_pos _loc T
  | {"σ" | "<sigma>"   | "<stack>"  } when p = `A -> in_pos _loc S
  | {"ο" | "<omicron>" | "<prop>"   } when p = `A -> in_pos _loc P
  | {"κ" | "<kappa>"   | "<ordinal>"} when p = `A -> in_pos _loc O
  | id:ident                          when p = `A -> in_pos _loc (Var(id))
  | "(" s:(sort `F) ")"               when p = `A -> s
  | s1:(sort `A) _:arrow s2:(sort `F) when p = `F -> in_pos _loc (Fun(s1,s2))
  | s:(sort `A)                       when p = `F -> s
let sort = sort `F

let parser toplevel = "sort" id:ident '=' s:sort
