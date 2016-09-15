open Bindlib
open Util
open Ast

type proc = term * stac

exception Runtime_error of string
let runtime_error : type a. string -> a = fun msg -> raise (Runtime_error msg)

let step : proc -> proc option = function
  | (Valu(v)          , Epsi      ) -> None
  | (Appl(t,u)        , pi        ) -> Some (u, Fram(t,pi))
  | (Valu(v)          , Fram(t,pi)) -> Some (t, Push(v,pi))
  | (Valu(LAbs(_,b))  , Push(v,pi)) -> Some (subst b v, pi)
  | (MAbs(b)          , pi        ) -> Some (subst b pi, pi)
  | (Name(pi,t)       , _         ) -> Some (t, pi)
  | (Proj(Reco(m),l)  , pi        ) ->
      begin
        try Some (Valu(M.find l m), pi)
        with Not_found -> runtime_error "Unknown record field"
      end
  | (Case(Cons(c,v),m), pi        ) ->
      begin
        try Some (subst (snd (M.find c m)) v, pi)
        with Not_found -> runtime_error "Unknown constructor"
      end
  | (FixY(t,v)        , pi        ) -> let f = fun x -> FixY(t,x) in
                                       let b = binder_from_fun "x" f in
                                       Some (t, Push(LAbs(None,b),Push(v,pi)))
  (* Runtime errors. *)
  | (Proj(_)          , _         ) -> runtime_error "invalid projection"
  | (Case(_,_)        , _         ) -> runtime_error "invalid case analysis"
  | (Vari(_)          , _         ) -> runtime_error "free term variable"
  | (Valu(_)          , _         ) -> runtime_error "free stack variable"
  | (HApp(_,_)        , _         ) -> runtime_error "higher-order"

let rec steps : proc -> proc = fun p ->
  match step p with
  | None   -> p
  | Some p -> steps p

let eval : term -> valu = fun t ->
  match steps (t, Epsi) with
  | (Valu v, Epsi) -> v
  | _              -> runtime_error "unexpected error"
