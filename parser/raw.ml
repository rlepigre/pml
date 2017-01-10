(** Parser level abstract syntax tree. This module defines the low level AST
    for the language. *)

open Bindlib
open Sorts
open Pos
open Ast
open Env
open Output

(* Log function registration. *)
let log_par = Log.register 'p' (Some "par") "syntax analysis"
let log_par = Log.(log_par.p)

type raw_sort = raw_sort' loc
and raw_sort' =
  | SV | ST | SS | SP | SO
  | SFun of raw_sort * raw_sort
  | SVar of string
  | SUni of raw_sort option ref

let print_raw_sort : out_channel -> raw_sort -> unit = fun ch s ->
  let rec print ch s =
    match s.elt with
    | SV        -> output_string ch "SV"
    | ST        -> output_string ch "ST"
    | SS        -> output_string ch "SS"
    | SP        -> output_string ch "SP"
    | SO        -> output_string ch "SO"
    | SFun(a,b) -> Printf.fprintf ch "SFun(%a,%a)" print a print b
    | SVar(x)   -> Printf.fprintf ch "SVar(%S)" x
    | SUni(r)   ->
        begin
          match !r with
          | None   -> output_string ch "SUni(None)"
          | Some a -> Printf.fprintf ch "SUni(Some(%a))" print a
        end
  in print ch s

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

let rec sort_repr : env -> raw_sort -> raw_sort = fun env s ->
  match s.elt with
  | SUni({contents = Some s}) -> sort_repr env s
  | SVar(x)                   ->
      begin
        try
          let Sort s = find_sort x env in
          sort_from_ast s
        with Not_found -> s
      end
  | _                         -> s

exception Unbound_sort of string * Pos.pos option
let unbound_sort : string -> Pos.pos option -> 'a =
  fun s p -> raise (Unbound_sort(s,p))

let rec unsugar_sort : env -> raw_sort -> any_sort = fun env s ->
  match (sort_repr env s).elt with
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

type flag = [`V | `T] ref

type 'a ne_list = 'a * 'a list
let ne_list_to_list : 'a ne_list -> 'a list = fun (x,xs) -> x::xs

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

  | ELAbs of (strloc * raw_ex option) ne_list * raw_ex
  | ECons of strloc * (raw_ex * flag) option
  | EReco of (strloc * raw_ex * flag) list
  | EScis
  | EAppl of raw_ex * raw_ex
  | EMAbs of (strloc * raw_ex option) ne_list * raw_ex
  | EName of raw_ex * raw_ex
  | EProj of raw_ex * flag * strloc
  | ECase of raw_ex * flag * (strloc * (strloc * raw_ex option) * raw_ex) list
  | EFixY of raw_ex
  | ECoer of raw_ex * raw_ex
  | ELamb of strloc * raw_sort * raw_ex

  | EEpsi
  | EPush of raw_ex * raw_ex
  | EFram of raw_ex * raw_ex

  | EConv
  | ESucc of raw_ex

let print_raw_expr : out_channel -> raw_ex -> unit = fun ch e ->
  let rec print ch e =
    match e.elt with
    | EVari(x,args) -> Printf.fprintf ch "EVari(%S,[%a])" x.elt
                         (Print.print_list print "; ") args
    | EHOFn(x,s,e)  -> Printf.fprintf ch "EHOFn(%S,%a,%a)" x.elt
                         print_raw_sort s print e
    | EFunc(a,b)    -> Printf.fprintf ch "EFunc(%a,%a)" print a print b
    | EProd(l)      -> Printf.fprintf ch "EProd([%a])"
                         (Print.print_list aux_ps "; ") l
    | EUnit         -> Printf.fprintf ch "EUnit"
    | EDSum(l)      -> Printf.fprintf ch "EDSum([%a])"
                         (Print.print_list aux_ps "; ") l
    | EUniv(x,s,a)  -> Printf.fprintf ch "EUniv(%S,%a,%a)" x.elt
                         print_raw_sort s print a
    | EExis(x,s,a)  -> Printf.fprintf ch "EExis(%S,%a,%a)" x.elt
                         print_raw_sort s print a
    | EFixM(o,x,a)  -> Printf.fprintf ch "EFixM(%a,%S,%a)"
                         print o x.elt print a
    | EFixN(o,x,a)  -> Printf.fprintf ch "EFixN(%a,%S,%a)"
                         print o x.elt print a
    | EMemb(t,a)    -> Printf.fprintf ch "EMemb(%a,%a)" print t print a
    | ERest(a,eq)   -> Printf.fprintf ch "ERest(%a,%a)" aux_opt a aux_eq eq
    | ELAbs(args,t) -> Printf.fprintf ch "ELAbs([%a],%a)"
                         (Print.print_list aux_arg "; ")
                         (ne_list_to_list args) print t
    | ECons(c,ao)   -> Printf.fprintf ch "ECons(%S,%a)" c.elt aux_cons ao
    | EReco(l)      -> Printf.fprintf ch "EReco([%a])"
                         (Print.print_list aux_rec "; ") l
    | EScis         -> Printf.fprintf ch "EScis"
    | EAppl(t,u)    -> Printf.fprintf ch "EAppl(%a,%a)" print t print u
    | EMAbs(args,t) -> Printf.fprintf ch "EMAbs([%a],%a)"
                         (Print.print_list aux_arg "; ")
                         (ne_list_to_list args) print t
    | EName(s,t)    -> Printf.fprintf ch "EName(%a,%a)" print s print t
    | EProj(v,_,l)  -> Printf.fprintf ch "EProj(%a,%S)" print v l.elt
    | ECase(v,_,l)  -> Printf.fprintf ch "ECase(%a,[%a])" print v
                         (Print.print_list aux_patt "; ") l
    | EFixY(t)      -> Printf.fprintf ch "EFixY(%a)" print t
    | ECoer(t,a)    -> Printf.fprintf ch "ECoer(%a,%a)" print t print a
    | ELamb(x,s,t)  -> Printf.fprintf ch "ELamb(%S,%a,%a)" x.elt
                         print_raw_sort s print t
    | EEpsi         -> Printf.fprintf ch "EEpsi"
    | EPush(v,s)    -> Printf.fprintf ch "EPush(%a,%a)" print v print s
    | EFram(t,s)    -> Printf.fprintf ch "EFram(%a,%a)" print t print s
    | EConv         -> Printf.fprintf ch "EConv"
    | ESucc(o)      -> Printf.fprintf ch "ESucc(%a)" print o
  and aux_ps ch (l,e) = Printf.fprintf ch "(%S,%a)" l.elt print e
  and aux_rec ch (l,e,_) = Printf.fprintf ch "(%S,%a)" l.elt print e
  and aux_cons ch = function
    | None      -> Printf.fprintf ch "None"
    | Some(e,_) -> Printf.fprintf ch "Some(%a)" print e
  and aux_opt ch = function
    | None    -> Printf.fprintf ch "None"
    | Some(e) -> Printf.fprintf ch "Some(%a)" print e
  and aux_eq ch (t,b,u) = Printf.fprintf ch "(%a,%b,%a)" print t b print u
  and aux_arg ch (s,ao) = Printf.fprintf ch "(%S,%a)" s.elt aux_opt ao
  and aux_patt ch (c,(x,ao),t) =
    Printf.fprintf ch "(%S,(%S,%a),%a)" c.elt x.elt aux_opt ao print t
  in print ch e

exception Unbound_variable of string * Pos.pos option
let unbound_var : string -> Pos.pos option -> 'a =
  fun s p -> raise (Unbound_variable(s,p))

exception Unification_failure of raw_ex
let unif_failure : raw_ex -> 'a =
  fun e -> raise (Unification_failure(e))

exception Sort_clash of raw_ex * raw_sort
let sort_clash : raw_ex -> raw_sort -> 'a =
  fun e s -> raise (Sort_clash(e,s))

exception Too_many_args of strloc
let too_many_args : strloc -> 'a =
  fun s -> raise (Too_many_args(s))

let rec eq_sort : env -> raw_sort -> raw_sort -> bool = fun env s1 s2 ->
  match ((sort_repr env s1).elt, (sort_repr env s2).elt) with
  | (SV         , SV         ) -> true
  | (ST         , ST         ) -> true
  | (SS         , SS         ) -> true
  | (SP         , SP         ) -> true
  | (SO         , SO         ) -> true
  | (SFun(s1,s2), SFun(k1,k2)) -> eq_sort env s1 k1 && eq_sort env s2 k2
  | (SUni(r1)   , SUni(r2)   ) -> r1 == r2
  | (SUni(r)    , _          ) -> r := Some s2; true
  | (_          , SUni(r)    ) -> r := Some s1; true
  | (_          , _          ) -> false

let infer_sorts : env -> raw_ex -> raw_sort -> unit = fun env e s ->
  let open Timed in
  let rec infer env vars e s =
    log_par "infer %a : %a" print_raw_expr e print_raw_sort s;
    match (e.elt, (sort_repr env s).elt) with
    | (EVari(x,args), _        ) ->
        begin
          try
            let (p,sx) =
              try M.find x.elt vars with Not_found ->
              let Expr(k,d) = find_expr x.elt env in
              (d.expr_def.pos, sort_from_ast k)
            in
            let nb_args = List.length args in
            let rec decompose acc nb s =
              match (nb, s.elt) with
              | (0, _        ) -> (List.rev acc, s)
              | (n, SFun(a,b)) -> decompose (a::acc) (n-1) b
              | (_, _        ) -> too_many_args x
            in
            let (ss, sx) = decompose [] nb_args sx in
            let rec infer_args args ss =
              match (args, ss) with
              | ([]     , []   ) -> ()
              | (a::args, s::ss) -> infer env vars a s; infer_args args ss
              | _                -> assert false
            in
            infer_args args ss;
            let sx_is_v = unsugar_sort env sx = Sort V in
            let s_is_t  = unsugar_sort env s  = Sort T in
            if not (eq_sort env sx s) && not (sx_is_v && s_is_t) then
              sort_clash e s
          with Not_found ->
            try
              ignore (find_value x.elt env);
            with Not_found ->
              unbound_var x.elt x.pos
        end
    | (EHOFn(x,k,f) , SFun(a,b)) -> if not (eq_sort env k a) then
                                      sort_clash e s;
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
    | (EUniv(x,k,e) , SP       )
    | (EExis(x,k,e) , SP       ) -> let vars = M.add x.elt (x.pos, k) vars in
                                    infer env vars e s
    | (EUniv(_,_,_) , SUni(r)  )
    | (EExis(_,_,_) , SUni(r)  ) -> r := Some _sp;
                                    infer env vars e s
    | (EUniv(_,_,_) , _        )
    | (EExis(_,_,_) , _        ) -> sort_clash e s
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
            M.add x.elt (x.pos, _sv) vs
          in
          let vars = List.fold_left fn vars (ne_list_to_list args) in
          infer env vars t _st
        end
    | (ELAbs(_,_)   , SUni(r)  ) -> r := Some _sv; infer env vars e s
    | (ELAbs(_,_)   , _        ) -> sort_clash e s
    | (ECons(_,vo)  , SV       ) ->
        begin
          match vo with
          | None       -> ()
          | Some (v,r) -> infer env vars v _sv; r := `V
        end
    | (ECons(_,vo)  , ST       ) ->
        begin
          match vo with
          | None       -> ()
          | Some (v,r) ->
              begin
                let tm = Time.save () in
                try infer env vars v _sv; r := `V
                with Sort_clash(_,_) ->
                  Time.rollback tm; infer env vars v _st; r := `T
              end
        end
    | (ECons(_,vo)  , SUni(r)  ) ->
        begin
          match vo with
          | None       -> r := Some _sv
          | Some (v,f) ->
              begin
                let tm = Time.save () in
                try infer env vars v _sv; f := `V; r := Some _sv
                with Sort_clash(_,_) ->
                  Time.rollback tm;
                  infer env vars v _st; f := `T; r := Some _st
              end
        end
    | (ECons(_,_)   , _        ) -> sort_clash e s
    | (EReco(l)     , SV       ) ->
        let fn (_,v,r) = infer env vars v _sv; r := `V in
        List.iter fn l
    | (EReco(l)     , ST       ) ->
        let fn (_,v,r) =
          let tm = Time.save () in
          try infer env vars v _sv; r := `V
          with Sort_clash(_,_) ->
            Time.rollback tm;
            infer env vars v _st; r := `T
        in
        List.iter fn l
    | (EReco(l)     , SUni(r)  ) ->
        let all_val = ref true in
        let fn (_,v,r) =
          let tm = Time.save () in
          try infer env vars v _sv; r := `V
          with Sort_clash(_,_) ->
            Time.rollback tm;
            infer env vars v _st; r := `T; all_val << false
        in
        List.iter fn l;
        r := Some (if !all_val then _sv else _st)
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
          let vars = List.fold_left fn vars (ne_list_to_list args) in
          infer env vars t _st
        end
    | (EMAbs(_,_)   , SUni(r)  ) -> r := Some _st; infer env vars e s
    | (EMAbs(_,_)   , _        ) -> sort_clash e s
    | (EName(s,t)   , ST       ) -> infer env vars s _ss; infer env vars t _st
    | (EName(_,_)   , SUni(r)  ) -> r := Some _st; infer env vars e s
    | (EName(_,_)   , _        ) -> sort_clash e s
    | (EProj(v,r,_) , ST       ) ->
        begin
          try infer env vars v _sv; r := `V
          with Sort_clash(_,_) ->
            infer env vars v _st; r := `T
        end
    | (EProj(_,_,_) , SUni(r)  ) -> r := Some _st; infer env vars e s
    | (EProj(_,_,_) , _        ) -> sort_clash e s
    | (ECase(v,r,l) , ST       ) ->
        begin
          let fn (_, (x, ao), t) =
            infer env (M.add x.elt (x.pos, Pos.none SV) vars) t _st;
            match ao with
            | None   -> ()
            | Some a -> infer env vars a _sp
          in
          List.iter fn l;
          let tm = Time.save () in
          try infer env vars v _sv; r := `V
          with Sort_clash(_,_) ->
            Time.rollback tm;
            infer env vars v _st; r := `T
        end
    | (ECase(_,_,_) , SUni(r)  ) -> r := Some _st; infer env vars e s
    | (ECase(_,_,_) , _        ) -> sort_clash e s
    | (EFixY(t)     , ST       )
    | (EFixY(t)     , SV       ) -> infer env vars t _st
    | (EFixY(_)     , SUni(r)  ) -> r := Some _sv; infer env vars e s
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

type boxed = Box : 'a sort * 'a ex loc bindbox -> boxed

let rec sort_filter : type a b. a sort -> boxed -> a box =
  fun s (Box(k,e)) ->
    match Sorts.eq_sort k s with
    | Eq  -> e
    | NEq -> Printf.printf "ERROR: %a ≠ %a\n%!"
               Print.print_sort s Print.print_sort k;
             assert false

let to_valu : boxed -> v box = sort_filter V

let to_term : boxed -> t box = fun e ->
  match e with
  | Box(T,e) -> e
  | Box(V,e) -> valu None e
  | _        -> assert false

let to_stac : boxed -> s box = sort_filter S
let to_prop : boxed -> p box = sort_filter P
let to_ordi : boxed -> o box = sort_filter O

let unsugar_expr : env -> raw_ex -> raw_sort -> boxed = fun env e s ->
  infer_sorts env e s;
  let rec unsugar env vars e s =
    log_par "unsug %a : %a" print_raw_expr e print_raw_sort s;
    match (e.elt, (sort_repr env s).elt) with
    | (EVari(x,args), _        ) ->
        begin
          try
            let box =
              try snd (M.find x.elt vars) with Not_found ->
              let Expr(sx, d) = find_expr x.elt env in
              Box(sx, box (build_pos x.pos (HDef(sx,d))))
            in
            let rec build_app (Box(se,e)) args =
              match (se, args) with
              | (F(sa,sb), a::args) ->
                  let sa' = sort_from_ast sa in
                  let a = sort_filter sa (unsugar env vars a sa') in
                  build_app (Box(sb, happ None sa e a)) args
              | (_       , []     ) -> Box(se,e)
              | (_       , _      ) -> assert false
            in
            let Box(se,ex) = build_app box args in
            let Sort s = unsugar_sort env s in
            match Sorts.eq_sort s se with
            | Eq  -> Box(s, sort_filter s (Box(se,ex)))
            | NEq ->
                begin
                  match (s, se) with
                  | (T, V) -> Box(T, valu e.pos ex)
                  | (_, _) -> assert false
                end
          with Not_found ->
            let d = find_value x.elt env in
            if args <> [] then assert false; (* FIXME *)
            Box(V, box (build_pos x.pos (VDef(d))))
        end
    | (EHOFn(x,k,f) , SFun(a,b)) ->
        let Sort sa = unsugar_sort env a in
        let Sort sb = unsugar_sort env b in
        let fn xk =
          let xk = (x.pos, Box(sa, vari x.pos xk)) in
          let vars = M.add x.elt xk vars in
          sort_filter sb (unsugar env vars f b)
        in
        Box(F(sa,sb), hfun e.pos sa sb x fn)
    (* Propositions. *)
    | (EFunc(a,b)   , SP       ) ->
        let a = unsugar env vars a s in
        let b = unsugar env vars b s in
        Box(P, func e.pos (to_prop a) (to_prop b))
    | (EUnit        , SP       ) -> Box(P, prod e.pos M.empty)
    | (EUnit        , SV       ) -> Box(V, reco e.pos M.empty)
    | (EUnit        , ST       ) -> Box(T, valu e.pos (reco e.pos M.empty))
    | (EProd(l)     , SP       ) ->
        let fn (p, a) = (p.elt, (p.pos, to_prop (unsugar env vars a s))) in
        let gn m (k,v) =
          if M.mem k m then assert false;
          M.add k v m
        in
        let m = List.fold_left gn M.empty (List.map fn l) in
        Box(P, prod e.pos m)
    | (EDSum(l)     , SP       ) ->
        let fn (p, a) = (p.elt, (p.pos, to_prop (unsugar env vars a s))) in
        let gn m (k,v) =
          if M.mem k m then assert false;
          M.add k v m
        in
        let m = List.fold_left gn M.empty (List.map fn l) in
        Box(P, dsum e.pos m)
    | (EUniv(x,k,e) , SP       ) ->
        let Sort k = unsugar_sort env k in
        let fn xk : p box =
          let xk = (x.pos, Box(k, vari x.pos xk)) in
          let vars = M.add x.elt xk vars in
          to_prop (unsugar env vars e _sp)
        in
        Box(P, univ e.pos x k fn)
    | (EExis(x,k,e) , SP       ) ->
        let Sort k = unsugar_sort env k in
        let fn xk : p box =
          let xk = (x.pos, Box(k, vari x.pos xk)) in
          let vars = M.add x.elt xk vars in
          to_prop (unsugar env vars e _sp)
        in
        Box(P, exis e.pos x k fn)
    | (EFixM(o,x,e) , SP       ) ->
        let o = to_ordi (unsugar env vars o _so) in
        let fn xo : pbox =
          let xo = (x.pos, Box(P, vari x.pos xo)) in
          let vars = M.add x.elt xo vars in
          to_prop (unsugar env vars e _sp)
        in
        Box(P, fixm e.pos o x fn)
    | (EFixN(o,x,e) , SP       ) ->
        let o = to_ordi (unsugar env vars o _so) in
        let fn xo : pbox =
          let xo = (x.pos, Box(P, vari x.pos xo)) in
          let vars = M.add x.elt xo vars in
          to_prop (unsugar env vars e _sp)
        in
        Box(P, fixn e.pos o x fn)
    | (EMemb(t,a)   , SP       ) ->
        let t = to_term (unsugar env vars t _st) in
        let a = to_prop (unsugar env vars a _sp) in
        Box(P, memb e.pos t a)
    | (ERest(a,eq)  , SP       ) ->
        let a =
          match a with
          | None   -> prod e.pos M.empty
          | Some a -> to_prop (unsugar env vars a _sp)
        in
        let (t,b,u) = eq in
        let t = to_term (unsugar env vars t _st) in
        let u = to_term (unsugar env vars u _st) in
        Box(P, rest e.pos a (t,b,u))
    (* Values. *)
    | (ELAbs(args,t), SV       ) ->
        begin
          match args with
          | ((x,ao), []   ) ->
              let fn a = to_prop (unsugar env vars a _sp) in
              let ao = Option.map fn ao in
              let fn xx =
                let xx = (x.pos, Box(V, vari x.pos xx)) in
                let vars = M.add x.elt xx vars in
                to_term (unsugar env vars t _st)
              in
              Box(V, labs e.pos ao x fn)
          | (x     , y::xs) ->
              let t = build_pos e.pos (ELAbs((y,xs),t)) in
              let t = build_pos e.pos (ELAbs((x,[]),t)) in
              unsugar env vars t _sv
        end
    | (ECons(c,vo)  , SV       ) ->
        let v =
          match vo with
          | None       -> reco None M.empty
          | Some (v,_) -> to_valu (unsugar env vars v _sv)
        in
        Box(V, cons e.pos c v)
    | (EReco(l)     , SV       ) ->
        let fn (p,v,_) = (p.elt, (p.pos, to_valu (unsugar env vars v _sv))) in
        let gn m (k,v) =
          if M.mem k m then assert false;
          M.add k v m
        in
        let m = List.fold_left gn M.empty (List.map fn l) in
        Box(V, reco e.pos m)
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
        let t = to_term (unsugar env vars t _st) in
        let u = to_term (unsugar env vars u _st) in
        Box(T, appl e.pos t u)
    | (EMAbs(args,t), ST       ) ->
        begin
          match args with
          | ((x,ao), []   ) ->
              let fn a = to_prop (unsugar env vars a _sp) in
              let ao = Option.map fn ao in
              let fn xx =
                let xx = (x.pos, Box(S, vari x.pos xx)) in
                let vars = M.add x.elt xx vars in
                to_term (unsugar env vars t _st)
              in
              Box(T, mabs e.pos ao x fn)
          | (x     , y::xs) ->
              let t = build_pos e.pos (EMAbs((y,xs),t)) in
              let t = build_pos e.pos (EMAbs((x,[]),t)) in
              unsugar env vars t _st
        end
    | (EName(s,t)   , ST       ) ->
        let s = to_stac (unsugar env vars s _ss) in
        let t = to_term (unsugar env vars t _st) in
        Box(T, name e.pos s t)
    | (EProj(v,r,l) , ST       ) ->
        begin
          match !r with
          | `V -> let v = to_valu (unsugar env vars v _sv) in
                  Box(T, proj e.pos v l)
          | `T -> let t = to_term (unsugar env vars v _st) in
                  Box(T, t_proj e.pos t l)
        end
    | (ECase(v,r,l) , ST       ) ->
        begin
          let fn (c, (x, ao), t) = 
            let f xx =
              let xx = (x.pos, Box(V, vari x.pos xx)) in
              let vars = M.add x.elt xx vars in
              to_term (unsugar env vars t _st)
            in
            (c.elt, (c.pos, x, f))
          in
          let gn m (k,v) =
            if M.mem k m then assert false;
            M.add k v m
          in
          let m = List.fold_left gn M.empty (List.map fn l) in
          match !r with
          | `V -> let v = to_valu (unsugar env vars v _sv) in
                  Box(T, case e.pos v m)          
          | `T -> let t = to_term (unsugar env vars v _st) in
                  Box(T, t_case e.pos t m)
        end
    | (EFixY(t)     , SV       ) ->
        let t = to_term (unsugar env vars t _st) in
        let f xx = fixy e.pos t (vari None xx) in
        Box(V, labs e.pos None (Pos.none "x") f)
    | (EFixY(t)     , ST       ) ->
        let v = to_valu (unsugar env vars e _sv) in
        Box(T, valu e.pos v)
    | (ECoer(v,a)   , SV       ) ->
        let v = to_valu (unsugar env vars v _sv) in
        let a = to_prop (unsugar env vars a _sp) in
        Box(V, vtyp e.pos v a)
    | (ECoer(t,a)   , ST       ) ->
        let t = to_term (unsugar env vars t _st) in
        let a = to_prop (unsugar env vars a _sp) in
        Box(T, ttyp e.pos t a)
    | (ELamb(x,k,t) , SV       ) ->
        let Sort k = unsugar_sort env k in
        let f xx =
          let xx = (x.pos, Box(k, vari x.pos xx)) in
          let vars = M.add x.elt xx vars in
          to_valu (unsugar env vars t _sv)
        in
        Box(V, vlam e.pos x k f)
    | (ELamb(x,k,t) , ST       ) ->
        let Sort k = unsugar_sort env k in
        let f xx =
          let xx = (x.pos, Box(k, vari x.pos xx)) in
          let vars = M.add x.elt xx vars in
          to_term (unsugar env vars t _sv)
        in
        Box(T, tlam e.pos x k f)
    (* Stacks. *)
    | (EEpsi        , SS       ) -> Box(S, epsi e.pos)
    | (EPush(v,pi)  , SS       ) ->
        let v  = to_valu (unsugar env vars v  _sv) in
        let pi = to_stac (unsugar env vars pi _ss) in
        Box(S, push e.pos v pi)
    | (EFram(t,pi)  , SS       ) ->
        let t  = to_term (unsugar env vars t  _st) in
        let pi = to_stac (unsugar env vars pi _ss) in
        Box(S, fram e.pos t pi)
    (* Ordinals. *)
    | (EConv        , SO       ) -> Box(O, conv e.pos)
    | (ESucc(o)     , SO       ) ->
        let o = to_ordi (unsugar env vars o _so) in
        Box(O, succ e.pos o)
    | (_            , _        ) -> assert false
  in
  unsugar env M.empty e s

type toplevel =
  | Sort_def of strloc * raw_sort
  | Expr_def of strloc * raw_sort * raw_ex
  | Valu_def of strloc * raw_ex option * raw_ex
