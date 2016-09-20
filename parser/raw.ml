(** Parser level abstract syntax tree. This module defines the low level AST
    for the language. *)


open Pos
open Ast
open Env

type raw_sort = raw_sort' loc
and raw_sort' =
  | SV | ST | SS | SP | SO
  | SFun of raw_sort * raw_sort
  | SVar of string
  | SUni of raw_sort option ref

let _sv = Pos.none SV
let _st = Pos.none ST
let _ss = Pos.none SS
let _sp = Pos.none SP
let _so = Pos.none SO

let rec sort_from_ast : type a. a sort -> raw_sort = function
  | V      -> Pos.none SV
  | T      -> Pos.none ST
  | S      -> Pos.none SS
  | P      -> Pos.none SP
  | O      -> Pos.none SO
  | F(s,k) -> Pos.none (SFun(sort_from_ast s, sort_from_ast k))

let new_sort_uvar : unit -> raw_sort = fun () ->
  Pos.none (SUni (ref None))

let sort_from_opt : raw_sort option -> raw_sort = function
  | None   -> new_sort_uvar ()
  | Some s -> s

let rec sort_repr : raw_sort -> raw_sort = fun s ->
  match s.elt with
  | SUni({contents = Some s}) -> sort_repr s
  | _                         -> s

let is_fun : raw_sort -> bool = fun s ->
  match (sort_repr s).elt with
  | SFun(_,_) -> true
  | _         -> false

exception Unbound_sort of string * Pos.pos option
let unbound_sort : string -> Pos.pos option -> 'a =
  fun s p -> raise (Unbound_sort(s,p))

let rec unsugar_sort : env -> raw_sort -> any_sort = fun env s ->
  match (sort_repr s).elt with
  | SV          -> Sort V
  | ST          -> Sort T
  | SS          -> Sort S
  | SP          -> Sort P
  | SO          -> Sort O
  | SFun(o1,o2) ->
      begin
        match (unsugar_sort env o1, unsugar_sort env o2) with
        | (Sort o1, Sort o2) -> Sort (F(o1,o2))
      end
  | SVar(x)     ->
      begin
        try find_sort x env with Not_found -> unbound_sort x s.pos
      end
  | SUni(_)     -> assert false


type raw_ex = raw_ex' loc
and raw_ex' =
  | EVari of strloc * raw_ex list
  | EHOFn of strloc * raw_sort * raw_ex

  | EFunc of raw_ex * raw_ex
  | EProd of (strloc * raw_ex) list
  | EUnit (* Empty record as a type or a term *)
  | EDSum of (strloc * raw_ex) list
  | EUniv of strloc * raw_sort * raw_ex
  | EExis of strloc * raw_sort * raw_ex
  | EFixM of raw_ex * strloc * raw_ex
  | EFixN of raw_ex * strloc * raw_ex
  | EMemb of raw_ex * raw_ex
  | ERest of raw_ex option * (raw_ex * bool * raw_ex)
  | EDPrj of raw_ex * strloc

  | ELAbs of (strloc * raw_ex option) list * raw_ex
  | ECons of strloc * raw_ex option
  | EReco of (strloc * raw_ex) list
  | EScis
  | EAppl of raw_ex * raw_ex
  | EMAbs of (strloc * raw_ex option) list * raw_ex
  | EName of raw_ex * raw_ex
  | EProj of raw_ex * strloc
  | ECase of raw_ex * (strloc * (strloc * raw_ex option) * raw_ex) list
  | EFixY of raw_ex
  | ECoer of raw_ex * raw_ex
  | ELamb of strloc * raw_sort * raw_ex

  | EEpsi
  | EPush of raw_ex * raw_ex
  | EFram of raw_ex * raw_ex

  | EConv
  | ESucc of raw_ex

exception Unbound_variable of string * Pos.pos option
let unbound_var : string -> Pos.pos option -> 'a =
  fun s p -> raise (Unbound_variable(s,p))

exception Unification_failure of raw_ex
let unif_failure : raw_ex -> 'a =
  fun e -> raise (Unification_failure(e))

exception Sort_clash of raw_ex * raw_sort
let sort_clash : raw_ex -> raw_sort -> 'a =
  fun e s -> raise (Sort_clash(e,s))

let rec eq_sort : raw_sort -> raw_sort -> bool = fun s1 s2 ->
  match ((sort_repr s1).elt, (sort_repr s2).elt) with
  | (SV         , SV         ) -> true
  | (ST         , ST         ) -> true
  | (SS         , SS         ) -> true
  | (SP         , SP         ) -> true
  | (SO         , SO         ) -> true
  | (SFun(s1,s2), SFun(k1,k2)) -> eq_sort s1 k1 && eq_sort s2 k2
  | (SUni(r1)   , SUni(r2)   ) -> r1 == r2
  | (SUni(r)    , _          ) -> r := Some s2; true
  | (_          , SUni(r)    ) -> r := Some s1; true
  | (_          , _          ) -> false

let infer_sorts : env -> raw_ex -> raw_sort -> unit = fun env e s ->
  let open Timed in
  let rec infer env vars e s =
    match (e.elt, (sort_repr s).elt) with
    | (EVari(x,args), _        ) ->
        begin
          try
            let (p,k) = M.find x.elt vars in
            ignore (p,k);
            assert false (* TODO *)
          with Not_found ->
          try
            let Expr(k,_) = find_expr x.elt env in
            let k = sort_from_ast k in
            ignore k; assert false (* TODO *)
          with Not_found -> unbound_var x.elt x.pos
        end
    | (EHOFn(x,k,f) , SFun(a,b)) -> if not (eq_sort k a) then sort_clash e s;
                                    let vars = M.add x.elt (x.pos, k) vars in
                                    infer env vars f b
    | (EHOFn(_,_,_) , SUni(r)  ) -> let a = new_sort_uvar () in
                                    let b = new_sort_uvar () in
                                    r := Some (Pos.none (SFun(a,b)));
                                    infer env vars e s
    | (EHOFn(_,_,_) , _        ) -> sort_clash e s
    (* Propositions. *)
    | (EFunc(a,b)   , SP       ) -> infer env vars a _sp; infer env vars b _sp
    | (EFunc(_,_)   , SUni(r)  ) -> r := Some _sp; infer env vars e s
    | (EFunc(_,_)   , _        ) -> sort_clash e s
    | (EUnit        , SP       )
    | (EUnit        , SV       )
    | (EUnit        , ST       ) -> ()
    | (EUnit        , SUni(_)  ) -> unif_failure e
    | (EUnit        , _        ) -> sort_clash e s
    | (EDSum(l)     , SP       )
    | (EProd(l)     , SP       ) -> let fn (_, a) =
                                      infer env vars a _sp
                                    in List.iter fn l
    | (EDSum(_)     , SUni(r)  )
    | (EProd(_)     , SUni(r)  ) -> r := Some _sp;
                                    infer env vars e s
    | (EDSum(_)     , _        )
    | (EProd(_)     , _        ) -> sort_clash e s
    | (EUniv(x,k,e) , _        )
    | (EExis(x,k,e) , _        ) -> let vars = M.add x.elt (x.pos, k) vars in
                                    infer env vars e s
    | (EFixM(o,x,e) , SP       )
    | (EFixN(o,x,e) , SP       ) -> infer env vars o _so;
                                    let vars = M.add x.elt (x.pos,_so) vars in
                                    infer env vars e _sp
    | (EFixM(_,_,_) , SUni(r)  )
    | (EFixN(_,_,_) , SUni(r)  ) -> r := Some _sp; infer env vars e s
    | (EFixM(_,_,_) , _        )
    | (EFixN(_,_,_) , _        ) -> sort_clash e s
    | (EMemb(t,a)   , SP       ) -> infer env vars t _st; infer env vars a _sp
    | (EMemb(t,a)   , SUni(r)  ) -> r := Some _sp; infer env vars e s
    | (EMemb(_,_)   , _        ) -> sort_clash e s
    | (ERest(a,eq)  , SP       ) ->
        let (t,_,u) = eq in
        infer env vars t _st;
        infer env vars u _st;
        begin
          match a with
          | None   -> ()
          | Some a -> infer env vars a _sp
        end
    | (ERest(_,_)   , SUni(r)  ) -> r := Some _sp; infer env vars e s
    | (ERest(_,_)   , _        ) -> sort_clash e s
    | (EDPrj(t,x)   , SP       ) -> infer env vars t _st
    | (EDPrj(_,_)   , SUni(r)  ) -> r := Some _sp; infer env vars e s
    | (EDPrj(_,_)   , _        ) -> sort_clash e s
    (* Terms / Values. *)
    | (ELAbs(args,t), SV       )
    | (ELAbs(args,t), ST       ) ->
        begin
          let fn vs (x, ao) =
            begin
              match ao with
              | None   -> ()
              | Some a -> infer env vars a _sp
            end;
            M.add x.elt (x.pos, Pos.none SV) vs
          in
          let vars = List.fold_left fn vars args in
          infer env vars t _st
        end
    | (ELAbs(_,_)   , SUni(r)  ) -> r := Some _sv; infer env vars e s
    | (ELAbs(_,_)   , _        ) -> sort_clash e s
    | (ECons(_,vo)  , SV       )
    | (ECons(_,vo)  , ST       ) ->
        begin
          match vo with
          | None   -> ()
          | Some v ->
              begin
                let tm = Time.save () in
                try infer env vars v _sv
                with Sort_clash(_,_) ->
                  Time.rollback tm;
                  infer env vars v _st
              end
        end
    | (ECons(_,vo)  , SUni(r)  ) ->
        begin
          match vo with
          | None   -> r := Some _sv
          | Some v -> infer env vars v s
        end
    | (ECons(_,_)   , _        ) -> sort_clash e s
    | (EReco(l)     , SV       )
    | (EReco(l)     , ST       ) ->
        List.iter (fun (_,v) -> infer env vars v s) l
    | (EReco(l)     , SUni(r)  ) ->
        begin
          let tm = Time.save () in
          try
            List.iter (fun (_,v) -> infer env vars v _sv) l;
            r := Some _sv
          with Sort_clash(_,_) ->
            Time.rollback tm;
            r := Some _st;
            infer env vars e s
        end
    | (EReco(_)     , _        ) -> sort_clash e s
    | (EScis        , SV       )
    | (EScis        , ST       ) -> ()
    | (EScis        , SUni(r)  ) -> r := Some _sv; infer env vars e s
    | (EScis        , _        ) -> sort_clash e s
    | (EAppl(t,u)   , ST       ) -> infer env vars t s; infer env vars u s
    | (EAppl(_,_)   , SUni(r)  ) -> r := Some _st; infer env vars e s
    | (EAppl(_,_)   , _        ) -> sort_clash e s
    | (EMAbs(args,t), ST       ) ->
        begin
          let fn vs (x, ao) =
            begin
              match ao with
              | None   -> ()
              | Some a -> infer env vars a _sp
            end;
            M.add x.elt (x.pos, Pos.none SS) vs
          in
          let vars = List.fold_left fn vars args in
          infer env vars t _st
        end
    | (EMAbs(_,_)   , SUni(r)  ) -> r := Some _st; infer env vars e s
    | (EMAbs(_,_)   , _        ) -> sort_clash e s
    | (EName(s,t)   , ST       ) -> infer env vars s _ss; infer env vars t _st
    | (EName(_,_)   , SUni(r)  ) -> r := Some _st; infer env vars e s
    | (EName(_,_)   , _        ) -> sort_clash e s
    | (EProj(v,_)   , ST       ) -> infer env vars v _sv
    | (EProj(v,_)   , SUni(r)  ) -> r := Some _st; infer env vars e s
    | (EProj(_,_)   , _        ) -> sort_clash e s
    | (ECase(v,l)   , ST       ) ->
        begin
          let fn (_, (x, ao), t) =
            infer env (M.add x.elt (x.pos, Pos.none SV) vars) t _st;
            match ao with
            | None   -> ()
            | Some a -> infer env vars a _sp
          in
          List.iter fn l;
          let tm = Time.save () in
          try infer env vars v _sv;
          with Sort_clash(_,_) ->
            Time.rollback tm;
            infer env vars v _st;
        end
    | (ECase(_,_)   , SUni(r)  ) -> r := Some _st; infer env vars e s
    | (ECase(_,_)   , _        ) -> sort_clash e s
    | (EFixY(t)     , ST       ) -> infer env vars t s
    | (EFixY(_)     , SUni(r)  ) -> r := Some _st; infer env vars e s
    | (EFixY(_)     , _        ) -> sort_clash e s
    | (ECoer(t,a)   , SV       )
    | (ECoer(t,a)   , ST       ) -> infer env vars t s; infer env vars a _sp
    | (ECoer(t,a)   , SUni(r)  ) -> infer env vars t s; infer env vars a _sp
    | (ECoer(t,_)   , _        ) -> sort_clash e s
    | (ELamb(x,k,t) , _        ) -> infer env (M.add x.elt (x.pos,k) vars) t s
    (* Stacks. *)
    | (EEpsi        , SS       ) -> ()
    | (EPush(v,s)   , SS       ) -> infer env vars v _sv; infer env vars s _ss
    | (EFram(t,s)   , SS       ) -> infer env vars t _st; infer env vars s _ss
    | (EEpsi        , SUni(r)  )
    | (EPush(_,_)   , SUni(r)  )
    | (EFram(_,_)   , SUni(r)  ) -> r := Some _ss; infer env vars e s
    | (EEpsi        , _        )
    | (EPush(_,_)   , _        )
    | (EFram(_,_)   , _        ) -> sort_clash e s
    (* Ordinals. *)
    | (EConv        , SO       ) -> ()
    | (ESucc(o)     , SO       ) -> infer env vars o s
    | (EConv        , SUni(r)  )
    | (ESucc(_)     , SUni(r)  ) -> r := Some _so; infer env vars e s
    | (EConv        , _        )
    | (ESucc(_)     , _        ) -> sort_clash e s
  in infer env M.empty e s

open Bindlib
type boxed = Box : 'a sort * 'a ex loc bindbox -> boxed

let unsugar_expr : env -> raw_ex -> raw_sort -> any_expr = fun env e s ->
  infer_sorts env e s;
  let rec unsugar env vars e s =
    match (e.elt, (sort_repr s).elt) with
    | (EVari(x,args), _        ) -> assert false (* TODO *)
    | (EHOFn(x,k,f) , SFun(a,b)) -> assert false (* TODO *)
    (* Propositions. *)
    | (EFunc(a,b)   , SP       ) ->
        begin
          match (unsugar env vars a s, unsugar env vars a s) with
          | (Box(P,a), Box(P,b)) -> Box(P, func e.pos a b)
          | _                    -> assert false
        end
    | (EUnit        , SP       ) -> Box(P, prod e.pos M.empty)
    | (EUnit        , SV       ) -> Box(V, reco e.pos M.empty)
    | (EUnit        , ST       ) -> Box(T, valu e.pos (reco e.pos M.empty))
    | (EProd(l)     , SP       ) ->
        let fn (p, a) : (string * (pos option * p ex loc bindbox)) =
          match unsugar env vars a s with
          | Box(P,a) -> (p.elt, (p.pos, a))
          | _        -> assert false
        in
        let gn m (k,v) =
          if M.mem k m then assert false;
          M.add k v m
        in
        let m = List.fold_left gn M.empty (List.map fn l) in
        Box(P, prod e.pos m)
    | (EDSum(l)     , SP       ) ->
        let fn (p, a) : (string * (pos option * p ex loc bindbox)) =
          match unsugar env vars a s with
          | Box(P,a) -> (p.elt, (p.pos, a))
          | _        -> assert false
        in
        let gn m (k,v) =
          if M.mem k m then assert false;
          M.add k v m
        in
        let m = List.fold_left gn M.empty (List.map fn l) in
        Box(P, dsum e.pos m)
    | (EUniv(x,k,e) , _        ) -> assert false (* TODO *)
    | (EExis(x,k,e) , _        ) -> assert false (* TODO *)
    | (EFixM(o,x,e) , SP       ) -> assert false (* TODO *)
    | (EFixN(o,x,e) , SP       ) -> assert false (* TODO *)
    | (EMemb(t,a)   , SP       ) ->
        begin
          match (unsugar env vars t _st, unsugar env vars a _sp) with
          | (Box(T,t), Box(P,a)) -> Box(P, memb e.pos t a)
          | _                    -> assert false
        end
    | (ERest(a,eq)  , SP       ) ->
        begin
          let a : p ex loc bindbox =
            match a with
            | None   -> prod e.pos M.empty
            | Some a ->
                begin
                  match unsugar env vars a _sp with
                  | Box(P,a) -> a
                  | _        -> assert false
                end
          in
          let (t,b,u) = eq in
          match (unsugar env vars t _st, unsugar env vars u _st) with
          | (Box(T,t), Box(T,u)) -> Box(P, rest e.pos a (t,b,u))
          | _                    -> assert false
        end
    | (EDPrj(t,x)   , SP       ) ->
        begin
          match unsugar env vars t _st with
          | Box(T,t) -> Box(P, dprj e.pos t x)
          | _        -> assert false
        end
    (* Values. *)
    | (ELAbs(args,t), SV       ) -> assert false (* TODO *)
    | (ECons(_,vo)  , SV       ) -> assert false (* TODO *)
    | (EReco(l)     , SV       ) -> assert false (* TODO *)
    | (EScis        , SV       ) -> Box(V, scis e.pos)
    (* Values as terms. *)
    | (ELAbs(_,_)   , ST       )
    | (ECons(_,_)   , ST       )
    | (EReco(_)     , ST       )
    | (EScis        , ST       ) ->
        begin
          match unsugar env vars e _sv with
          | Box(V,v) -> Box(T, valu e.pos v)
          | _        -> assert false
        end
    (* Terms. *)
    | (EAppl(t,u)   , ST       ) ->
        begin
          match (unsugar env vars t _st, unsugar env vars u _st) with
          | (Box(T,t), Box(T,u)) -> Box(T, appl e.pos t u)
          | _                    -> assert false
        end
    | (EMAbs(args,t), ST       ) -> assert false (* TODO *)
    | (EName(s,t)   , ST       ) ->
        begin
          match (unsugar env vars s _ss, unsugar env vars t _st) with
          | (Box(S,s), Box(T,t)) -> Box(T, name e.pos s t)
          | _                    -> assert false
        end
    | (EProj(v,_)   , ST       ) -> assert false (* TODO *)
    | (ECase(v,l)   , ST       ) -> assert false (* TODO *)
    | (EFixY(t)     , ST       ) -> assert false (* TODO *)
    | (ECoer(t,a)   , SV       ) -> assert false (* TODO *)
    | (ECoer(t,a)   , ST       ) -> assert false (* TODO *)
    | (ELamb(x,k,t) , _        ) -> assert false (* TODO *)
    (* Stacks. *)
    | (EEpsi        , SS       ) -> Box(S, epsi e.pos)
    | (EPush(v,pi)  , SS       ) ->
        begin
          match (unsugar env vars v s, unsugar env vars pi s) with
          | (Box(V,v), Box(S,pi)) -> Box(S, push e.pos v pi)
          | _                     -> assert false
        end
    | (EFram(t,pi)  , SS       ) ->
        begin
          match (unsugar env vars t s, unsugar env vars pi s) with
          | (Box(T,t), Box(S,pi)) -> Box(S, fram e.pos t pi)
          | _                     -> assert false
        end
    (* Ordinals. *)
    | (EConv        , SO       ) -> Box(O, conv e.pos)
    | (ESucc(o)     , SO       ) ->
        begin
          match unsugar env vars o s with
          | Box(O,o) -> Box(O, succ e.pos o)
          | _        -> assert false
        end
    | (_            , _        ) -> assert false
  in
  match unsugar env M.empty e s with Box(s, e) -> Expr(s, unbox e)

type toplevel =
  | Sort_def of strloc * raw_sort
  | Expr_def of strloc * raw_sort * raw_ex
