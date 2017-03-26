open Sorts
open Eval
open Ast
open Pos

type any_sort = Sort : 'a sort           -> any_sort
type any_expr = Expr : 'a sort * 'a expr -> any_expr

module SMap = Map.Make(String)

type env =
  { sorts  : any_sort SMap.t
  ; exprs  : any_expr SMap.t
  ; values : value SMap.t }

let empty =
  { sorts  = SMap.empty
  ; exprs  = SMap.empty
  ; values = SMap.empty }

let find_sort : string -> env -> any_sort =
  fun id env -> SMap.find id env.sorts

let find_expr : string -> env -> any_expr =
  fun id env -> SMap.find id env.exprs

let find_value : string -> env -> value =
  fun id env -> SMap.find id env.values

let add_sort : type a. string -> a sort -> env -> env =
  fun id s env -> {env with sorts = SMap.add id (Sort s) env.sorts}

let add_expr : type a. strloc -> a sort -> a box -> env -> env =
  fun expr_name s expr_box env ->
    let expr_def = Bindlib.unbox expr_box in
    let ex = Expr(s, {expr_name; expr_def}) in
    {env with exprs = SMap.add expr_name.elt ex env.exprs}

let add_value : strloc -> term -> prop -> e_valu -> env -> env =
  fun value_name value_orig value_type value_eval env ->
    let nv = {value_name; value_type; value_orig; value_eval} in
    {env with values = SMap.add value_name.elt nv env.values}
