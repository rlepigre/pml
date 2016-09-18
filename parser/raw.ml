(** Parser level abstract syntax tree. This module defines the low level AST
    for the language. *)


open Pos

module Sort =
  struct
    type sort = sort' loc
    and sort' = V | T | S | P | O | Fun of sort * sort | Var of string

    let is_fun : sort -> bool =
      fun s ->
        match s.elt with
        | Fun(_,_) -> true
        | _        -> false

    let print ch s =
      let rec print ch s =
        match s.elt with
        | V           -> output_string ch "ι"
        | T           -> output_string ch "τ"
        | S           -> output_string ch "σ"
        | P           -> output_string ch "ο"
        | O           -> output_string ch "κ"
        | Var(id)     -> output_string ch id
        | Fun(s1, s2) ->
            if is_fun s1 then Printf.fprintf ch "(%a) → %a" print s1 print s2
            else Printf.fprintf ch "%a → %a" print s1 print s2
      in print ch s
  end

module Expr =
  struct
    type expr = expr' loc
    and expr' =
      | EVari of strloc * expr list

      | EFunc of expr * expr
      | EProd of (strloc * expr) list
      | EUniv of strloc * Sort.sort * expr
      | EExis of strloc * Sort.sort * expr
      | EFixM of expr * strloc * expr
      | EFixN of expr * strloc * expr
      | EMemb of expr * expr
      | ERest of expr option * (expr * bool * expr)
      | EDPrj of expr * strloc

      | ELAbs of (strloc * expr option) list * expr
      | ECons of strloc * expr option
      | EReco of (strloc * expr) list
      | EScis
      | EAppl of expr * expr
      | EMAbs of (strloc * expr option) list * expr
      | EName of expr * expr
      | EProj of expr * strloc
      | ECase of expr * (strloc * (strloc * expr option) * expr) list
      | EFixY of expr
      | ECoer of expr * expr
      | ELamb of strloc * Sort.sort * expr

      | EEpsi
      | EPush of expr * expr
      | EFram of expr * expr

      | EConv
      | ESucc of expr
  end

type toplevel =
  | Sort_def of strloc * Sort.sort
  | Expr_def of strloc * Expr.expr
