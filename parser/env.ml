open Ast
open Pos

type any_sort = Sort : 'a sort                      -> any_sort
type any_expr = Expr : 'a sort * 'a ex loc * 'a box -> any_expr

type env =
  { sorts : any_sort M.t
  ; exprs : any_expr M.t }

let empty =
  { sorts = M.empty
  ; exprs = M.empty }

let find_sort : string -> env -> any_sort =
  fun id env -> M.find id env.sorts

let find_expr : string -> env -> any_expr =
  fun id env -> M.find id env.exprs

let add_sort : type a. string -> a sort -> env -> env =
  fun id s env -> {env with sorts = M.add id (Sort s) env.sorts}

let add_expr : type a. string -> a sort -> a box -> env -> env =
  fun id s bx env ->
    {env with exprs = M.add id (Expr(s, Bindlib.unbox bx, bx)) env.exprs}
