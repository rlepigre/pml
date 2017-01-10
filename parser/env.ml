open Sorts
open Ast
open Pos

type any_sort = Sort : 'a sort           -> any_sort
type any_expr = Expr : 'a sort * 'a expr -> any_expr

type value =
  { value_name : string
  ; value_type : prop
  ; value_orig : term }

type env =
  { sorts  : any_sort M.t
  ; exprs  : any_expr M.t
  ; values : value M.t }

let empty =
  { sorts  = M.empty
  ; exprs  = M.empty
  ; values = M.empty }

let find_sort : string -> env -> any_sort =
  fun id env -> M.find id env.sorts

let find_expr : string -> env -> any_expr =
  fun id env -> M.find id env.exprs

let find_value : string -> env -> value =
  fun id env -> M.find id env.values

let add_sort : type a. string -> a sort -> env -> env =
  fun id s env -> {env with sorts = M.add id (Sort s) env.sorts}

let add_expr : type a. strloc -> a sort -> a box -> env -> env =
  fun expr_name s expr_box env ->
    let expr_def = Bindlib.unbox expr_box in
    let ex = Expr(s, {expr_name; expr_def; expr_box}) in
    {env with exprs = M.add expr_name.elt ex env.exprs}

let add_value : string -> term -> prop -> env -> env =
  fun value_name value_orig value_type env ->
    let nv = {value_name; value_type; value_orig} in
    {env with values = M.add value_name nv env.values}
