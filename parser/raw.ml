(** Parser level abstract syntax tree. This module defines the low level (raw)
    AST for the language. This is where most syntactic sugars are applied. *)


open Output
open Extra
open Sorts
open Ast
open Pos
open Env

(* Log function registration. *)
let log_par = Log.register 'p' (Some "par") "syntax analysis"
let log_par = Log.(log_par.p)

type raw_sort = raw_sort' loc
and raw_sort' =
  | ST | SS | SP | SO
  (* The argument to SV is used to store terms for the syntactic
     sugar allowing terms in place where value are expected *)
  | SV of (vvar * tbox) list ref option
  | SFun of raw_sort * raw_sort
  | SVar of string
  | SUni of suvar
and suvar = int * strloc option * raw_sort option ref

let print_raw_sort : out_channel -> raw_sort -> unit = fun ch s ->
  let open Printf in
  let rec print ch s =
    match s.elt with
    | SV _        -> output_string ch "SV"
    | ST          -> output_string ch "ST"
    | SS          -> output_string ch "SS"
    | SP          -> output_string ch "SP"
    | SO          -> output_string ch "SO"
    | SFun(a,b)   -> fprintf ch "SFun(%a,%a)" print a print b
    | SVar(x)     -> fprintf ch "SVar(%S)" x
    | SUni(i,_,r) ->
        begin
          match !r with
          | None   -> fprintf ch "SUni(%i,None)" i
          | Some a -> fprintf ch "SUni(%i,Some(%a))" i print a
        end
  in print ch s

let pretty_print_raw_sort : out_channel -> raw_sort -> unit = fun ch s ->
  let rec is_fun s =
    match s.elt with
    | SFun(_,_)   -> true
    | SUni(i,_,r) ->
        begin
          match !r with
          | None   -> false
          | Some s -> is_fun s
        end
    | _           -> false
  in
  let rec print ch s =
    let open Printf in
    match s.elt with
    | SV _        -> output_string ch "ι"
    | ST          -> output_string ch "τ"
    | SS          -> output_string ch "σ"
    | SP          -> output_string ch "ο"
    | SO          -> output_string ch "κ"
    | SFun(a,b)   -> let (l,r) = if is_fun a then ("(",")") else ("","") in
                     fprintf ch "%s%a%s→%a" l print a r print b
    | SVar(x)     -> output_string ch x
    | SUni(i,_,r) ->
        begin
          match !r with
          | None   -> fprintf ch "?%i" i
          | Some a -> print ch a
        end
  in print ch s

let  sv = SV None
let _sv = Pos.none sv
let _sv_store l = Pos.none (SV (Some l))
let _st = Pos.none ST
let _ss = Pos.none SS
let _sp = Pos.none SP
let _so = Pos.none SO

let rec sort_from_ast : type a. a sort -> raw_sort = function
  | V      -> _sv
  | T      -> _st
  | S      -> _ss
  | P      -> _sp
  | O      -> _so
  | F(s,k) -> Pos.none (SFun(sort_from_ast s, sort_from_ast k))

let new_sort_uvar : strloc option -> raw_sort =
  let i = ref (-1) in
  fun x ->
    incr i;
    log_par "?%i is introduced" !i;
    Pos.none (SUni (!i, x, ref None))

let sort_uvar_set : suvar -> raw_sort -> unit =
  fun (i,_,r) v ->
    assert(!r = None);
    log_par "?%i := %a" i print_raw_sort v;
    r := Some v

let sort_from_opt : raw_sort option -> raw_sort = fun so ->
  match so with
  | None   -> new_sort_uvar None
  | Some s -> s

let rec sort_repr : env -> raw_sort -> raw_sort = fun env s ->
  match s.elt with
  | SUni(_,_,{contents = Some s}) -> sort_repr env s
  | SVar(x)                       ->
      begin
        try
          let Sort s = find_sort x env in
          sort_from_ast s
        with Not_found -> s
      end
  | _                             -> s

exception Unbound_sort of string * Pos.pos option
let unbound_sort : string -> Pos.pos option -> 'a =
  fun s p -> raise (Unbound_sort(s,p))

let rec unsugar_sort : env -> raw_sort -> any_sort = fun env s ->
  match (sort_repr env s).elt with
  | SV _        -> Sort V
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
  | SUni(r)     -> sort_uvar_set r _sp; Sort P

type flag = [`V | `T] ref

type 'a ne_list = 'a * 'a list
let ne_list_to_list : 'a ne_list -> 'a list = fun (x,xs) -> x::xs

let map_ne_list : ('a -> 'b) -> 'a ne_list -> 'b ne_list =
  fun f (x,xs) -> (f x, List.map f xs)

type raw_ex = raw_ex' loc
and raw_cond =
  | EEquiv of (raw_ex * bool * raw_ex)
  | ENoBox of raw_ex

and raw_ex' =
  | EVari of strloc * raw_sort
  | EHOAp of raw_ex * raw_sort * raw_ex list
  | EHOFn of strloc * raw_sort * raw_ex

  | EFunc of Totality.tot * raw_ex * raw_ex
  | EProd of (strloc * raw_ex) list * bool
  | EUnit (* Empty record as a type or a term *)
  | EDSum of (strloc * raw_ex option) list
  | EUniv of strloc ne_list * raw_sort * raw_ex
  | EExis of strloc ne_list * raw_sort * raw_ex
  | EFixM of raw_ex * strloc * raw_ex
  | EFixN of raw_ex * strloc * raw_ex
  | EMemb of raw_ex * raw_ex
  | ERest of raw_ex option * raw_cond
  | EImpl of raw_cond * raw_ex option

  | ELAbs of (strloc * raw_ex option) ne_list * raw_ex
  | ECons of strloc * (raw_ex * flag) option
  | EReco of (strloc * raw_ex * flag) list
  | EScis
  | EAppl of raw_ex * raw_ex
  | ESequ of raw_ex * raw_ex
  | EMAbs of strloc * raw_ex
  | EName of raw_ex * raw_ex
  | EProj of raw_ex * flag * strloc
  | ECase of raw_ex * flag * patt_ex list
  | EFixY of bool * strloc * raw_ex
  | EPrnt of string
  | ERepl of raw_ex * raw_ex * raw_ex
  | EDelm of raw_ex
  | ECoer of raw_sort * raw_ex * raw_ex
  | ESuch of raw_sort * (strloc * raw_sort) ne_list
                      * (strloc option * raw_ex) * raw_ex
  | EPSet of raw_sort * set_param * raw_ex

  | EConv
  | ESucc of raw_ex * int

  | EGoal of string

and patt_ex = (strloc * (strloc * raw_ex option) option) * raw_ex

let print_raw_expr : out_channel -> raw_ex -> unit = fun ch e ->
  let rec print ch e =
    match e.elt with
    | EVari(x,_)    -> Printf.fprintf ch "EVari(%S)" x.elt
    | EHOAp(e,_,es) -> Printf.fprintf ch "EHOAp(%a,[%a])" print e
                         (print_list print "; ") es
    | EHOFn(x,s,e)  -> Printf.fprintf ch "EHOFn(%S,%a,%a)" x.elt
                         print_raw_sort s print e
    | EFunc(t,a,b)  -> Printf.fprintf ch "EFunc(%a %a %a)"
                                      print a Print.arrow t print b
    | EProd(l,str)  -> Printf.fprintf ch "EProd([%a], %s)"
                         (print_list aux_ls "; ") l
                         (if str then "strict" else "extensible")
    | EUnit         -> Printf.fprintf ch "EUnit"
    | EDSum(l)      -> Printf.fprintf ch "EDSum([%a])"
                         (print_list aux_ps "; ") l
    | EUniv(xs,s,a) -> Printf.fprintf ch "EUniv([%a],%a,%a)"
                         (print_list aux_var ",") (ne_list_to_list xs)
                         print_raw_sort s print a
    | EExis(xs,s,a) -> Printf.fprintf ch "EExis([%a],%a,%a)"
                         (print_list aux_var ",") (ne_list_to_list xs)
                         print_raw_sort s print a
    | EFixM(o,x,a)  -> Printf.fprintf ch "EFixM(%a,%S,%a)"
                         print o x.elt print a
    | EFixN(o,x,a)  -> Printf.fprintf ch "EFixN(%a,%S,%a)"
                         print o x.elt print a
    | EMemb(t,a)    -> Printf.fprintf ch "EMemb(%a,%a)" print t print a
    | ERest(a,eq)   -> Printf.fprintf ch "ERest(%a,%a)" aux_opt a aux_eq eq
    | EImpl(eq,a)   -> Printf.fprintf ch "EImpl(%a,%a)" aux_opt a aux_eq eq
    | ELAbs(args,t) -> Printf.fprintf ch "ELAbs([%a],%a)"
                         (print_list aux_arg "; ")
                         (ne_list_to_list args) print t
    | ECons(c,ao)   -> Printf.fprintf ch "ECons(%S,%a)" c.elt aux_cons ao
    | EReco(l)      -> Printf.fprintf ch "EReco([%a])"
                         (print_list aux_rec "; ") l
    | EScis         -> Printf.fprintf ch "EScis"
    | EAppl(t,u)    -> Printf.fprintf ch "EAppl(%a,%a)" print t print u
    | ESequ(t,u)    -> Printf.fprintf ch "ESequ(%a,%a)" print t print u
    | EMAbs(arg,t)  -> Printf.fprintf ch "EMAbs(%a,%a)" aux_var arg print t
    | EName(s,t)    -> Printf.fprintf ch "EName(%a,%a)" print s print t
    | EProj(v,_,l)  -> Printf.fprintf ch "EProj(%a,%S)" print v l.elt
    | ECase(v,_,l)  -> Printf.fprintf ch "ECase(%a,[%a])" print v
                         (print_list aux_patt "; ") l
    | EFixY(s,a,t)  -> Printf.fprintf ch "EFixY(%b,%a,%a)" s aux_var a print t
    | EPrnt(s)      -> Printf.fprintf ch "EPrnt(%S)" s
    | ERepl(t,u,a)  -> Printf.fprintf ch "ERepl(%a,%a,%a)"
                         print t print u print a
    | EDelm(u)      -> Printf.fprintf ch "EDelm(%a)" print u
    | ECoer(_,t,a)  -> Printf.fprintf ch "ECoer(%a,%a)" print t print a
    | ESuch(_,v,j,u)-> let x = Option.default (Pos.none "_") (fst j) in
                       Printf.fprintf ch "ESuch(%a,%s,%a,%a)"
                         (print_list aux_sort ", ") (ne_list_to_list v)
                         x.elt print (snd j) print u
    | EPSet(_,l,u)  -> Printf.fprintf ch "EPSet(%a,%a)"
                         Print.print_set_param l print u
    | EConv         -> Printf.fprintf ch "EConv"
    | ESucc(o,n)    -> Printf.fprintf ch "ESucc(%a,%d)" print o n
    | EGoal(str)    -> Printf.fprintf ch "EGoal(%s)" str
  and aux_ls ch (l,e) = Printf.fprintf ch "(%S,%a)" l.elt print e
  and aux_ps ch (l,e) = Printf.fprintf ch "(%S,%a)" l.elt aux_opt e
  and aux_rec ch (l,e,_) = Printf.fprintf ch "(%S,%a)" l.elt print e
  and aux_var ch x = Printf.fprintf ch "%S" x.elt
  and aux_sort ch (x,s) = Printf.fprintf ch "%s:%a" x.elt print_raw_sort s
  and aux_cons ch = function
    | None      -> Printf.fprintf ch "None"
    | Some(e,_) -> Printf.fprintf ch "Some(%a)" print e
  and aux_opt ch = function
    | None    -> Printf.fprintf ch "None"
    | Some(e) -> Printf.fprintf ch "Some(%a)" print e
  and aux_eq ch = function
    | EEquiv(t,b,u) -> Printf.fprintf ch "(%a,%b,%a)" print t b print u
    | ENoBox(v)     -> Printf.fprintf ch "(%a↓)" print v
  and aux_arg ch (s,ao) = Printf.fprintf ch "(%S,%a)" s.elt aux_opt ao
  and aux_patt ch ((c,argo),t) =
    match argo with
    | None       -> Printf.fprintf ch "(%S,(_,None),%a)" c.elt print t
    | Some(x,ao) -> Printf.fprintf ch "(%S,(%S,%a),%a)" c.elt x.elt
                      aux_opt ao print t
  in print ch e

exception Unbound_variable of string * Pos.pos option
let unbound_var : string -> Pos.pos option -> 'a =
  fun s p -> raise (Unbound_variable(s,p))

exception Sort_clash of raw_ex * raw_sort
let sort_clash : raw_ex -> raw_sort -> 'a =
  fun e s -> raise (Sort_clash(e,s))

exception Too_many_args of raw_ex
let too_many_args : raw_ex -> 'a =
  fun s -> raise (Too_many_args(s))

exception Already_matched of strloc
let already_matched : strloc -> 'a =
  fun s -> raise (Already_matched(s))

let rec leq_sort : env -> raw_sort -> raw_sort -> bool = fun env s1 s2 ->
  log_par "leq_sort %a %a" print_raw_sort s1 print_raw_sort s2;
  let res =
  match ((sort_repr env s1).elt, (sort_repr env s2).elt) with
  | (SV _       , SV _       ) -> true
  | (ST         , ST         ) -> true
  | (SV _       , ST         ) -> true
  | (SS         , SS         ) -> true
  | (SP         , SP         ) -> true
  | (SO         , SO         ) -> true
  | (SFun(s1,s2), SFun(k1,k2)) -> leq_sort env k1 s1 && leq_sort env s2 k2
  | (SUni(r1)   , SUni(r2)   ) -> if r1 != r2 then sort_uvar_set r1 s2; true
  | (SUni(r)    , _          ) -> sort_uvar_set r s2; true
  | (_          , SUni(r)    ) -> sort_uvar_set r s1; true
  | (_          , _          ) -> false
  in log_par "ok"; res

let infer_sorts : env -> raw_ex -> raw_sort -> unit = fun env e s ->
  let open Timed in
  let rec infer env vars e s =
    log_par "infer %a : %a" print_raw_expr e print_raw_sort s;
    let leq u s = if not (leq_sort env u s) then sort_clash e s in
    match (e.elt, (sort_repr env s).elt) with
    | (EVari(x,sx)     , _        ) ->
        begin
          try
            let sy =
              try snd (M.find x.elt vars) with Not_found ->
                let Expr(k,d) = find_expr x.elt env in
                sort_from_ast k
            in
            leq sy sx; leq sx s
          with Not_found ->
            try
              ignore (find_value x.elt env);
              leq _sv sx; leq sx s
            with Not_found ->
              unbound_var x.elt x.pos
         end
    | (EHOAp(e,sx,es), _        ) ->
         let nb_args = List.length es in
         infer env vars e sx;
         let rec decompose acc nb s =
           let s = sort_repr env s in
           match (nb, s.elt) with
           | (0, _        ) -> (List.rev acc, s)
           | (n, SFun(a,b)) -> decompose (a::acc) (n-1) b
           | (n, SUni(r)  ) ->
              let a = new_sort_uvar None in
              let b = new_sort_uvar None in
              sort_uvar_set r (Pos.make s.pos (SFun(a,b)));
              decompose (a::acc) (n-1) b
           | (_, _        ) -> too_many_args e
         in
         let (ss, sx) = decompose [] nb_args sx in
         let rec infer_args args ss =
           match (args, ss) with
           | ([]     , []   ) -> ()
           | (a::args, s::ss) -> infer env vars a s; infer_args args ss
           | _                -> assert false
         in
         infer_args es ss;
         leq sx s
    | (EHOFn(x,k,f) , SFun(a,b)) -> leq a k;
                                    let vars = M.add x.elt (x.pos, k) vars in
                                    infer env vars f b
    | (EHOFn(_,_,_) , SUni(r)  ) -> let a = new_sort_uvar None in
                                    let b = new_sort_uvar None in
                                    sort_uvar_set r (Pos.none (SFun(a,b)));
                                    infer env vars e s
    | (EHOFn(_,_,_) , _        ) -> sort_clash e s
    (* Propositions. *)
    | (EFunc(_,a,b) , SP       ) -> infer env vars a _sp; infer env vars b _sp
    | (EFunc(_,_,_) , SUni(r)  ) -> sort_uvar_set r _sp; infer env vars e s
    | (EFunc(_,_,_) , _        ) -> sort_clash e s
    | (EUnit        , SP       )
    | (EUnit        , SV _     )
    | (EUnit        , ST       ) -> ()
    | (EUnit        , SUni(r)  ) -> sort_uvar_set r _sv; (* arbitrary *)
                                    infer env vars e s
    | (EUnit        , _        ) -> sort_clash e s
    | (EDSum(l)     , SP       ) -> let fn (_, a) =
                                      match a with
                                      | None   -> ()
                                      | Some a -> infer env vars a _sp
                                    in List.iter fn l
    | (EProd(l,_)   , SP       ) -> let fn (_, a) =
                                      infer env vars a _sp
                                    in List.iter fn l
    | (EDSum(_)     , SUni(r)  )
    | (EProd(_,_)   , SUni(r)  ) -> sort_uvar_set r _sp;
                                    infer env vars e s
    | (EDSum(_)     , _        )
    | (EProd(_,_)   , _        ) -> sort_clash e s
    | (EUniv(xs,k,e), SP       )
    | (EExis(xs,k,e), SP       ) -> let fn vars x =
                                      M.add x.elt (x.pos, k) vars
                                    in
                                    let xs = ne_list_to_list xs in
                                    let vars = List.fold_left fn vars xs in
                                    infer env vars e s
    | (EUniv(_,_,_) , SUni(r)  )
    | (EExis(_,_,_) , SUni(r)  ) -> sort_uvar_set r _sp;
                                    infer env vars e s
    | (EUniv(_,_,_) , _        )
    | (EExis(_,_,_) , _        ) -> sort_clash e s
    | (EFixM(o,x,e) , SP       )
    | (EFixN(o,x,e) , SP       ) -> infer env vars o _so;
                                    let vars = M.add x.elt (x.pos,_sp) vars in
                                    infer env vars e _sp
    | (EFixM(_,_,_) , SUni(r)  )
    | (EFixN(_,_,_) , SUni(r)  ) -> sort_uvar_set r _sp; infer env vars e s
    | (EFixM(_,_,_) , _        )
    | (EFixN(_,_,_) , _        ) -> sort_clash e s
    | (EMemb(t,a)   , SP       ) -> infer env vars t _st; infer env vars a _sp
    | (EMemb(t,a)   , SUni(r)  ) -> sort_uvar_set r _sp; infer env vars e s
    | (EMemb(_,_)   , _        ) -> sort_clash e s
    | (ERest(a,eq)  , SP       ) ->
       begin
         match eq with
         | EEquiv(t,_,u) ->
            infer env vars t _st;
            infer env vars u _st;
         | ENoBox(v) ->
            infer env vars v _sv;
       end;
       begin
         match a with
         | None   -> ()
         | Some a -> infer env vars a _sp
       end
    | (EImpl(eq,a)  , SP       ) ->
       begin
         match eq with
         | EEquiv(t,_,u) ->
            infer env vars t _st;
            infer env vars u _st;
         | ENoBox(v) ->
            infer env vars v _sv;
       end;
       begin
         match a with
         | None   -> ()
         | Some a -> infer env vars a _sp
       end
    | (ERest(_,_)   , SUni(r)  ) -> sort_uvar_set r _sp; infer env vars e s
    | (ERest(_,_)   , _        ) -> sort_clash e s
    | (EImpl(_,_)   , SUni(r)  ) -> sort_uvar_set r _sp; infer env vars e s
    | (EImpl(_,_)   , _        ) -> sort_clash e s
    (* Terms / Values. *)
    | (ELAbs(args,t), SV _     )
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
    | (ELAbs(_,_)   , SUni(r)  ) -> sort_uvar_set r _sv; infer env vars e s
    | (ELAbs(_,_)   , _        ) -> sort_clash e s
    | (ECons(_,vo)  , SV _     ) ->
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
          | None       -> sort_uvar_set r _sv
          | Some (v,f) ->
              begin
                let tm = Time.save () in
                try infer env vars v _sv; f := `V; sort_uvar_set r _sv
                with Sort_clash(_,_) ->
                  Time.rollback tm;
                  infer env vars v _st; f := `T; sort_uvar_set r _st
              end
        end
    | (ECons(_,_)   , _        ) -> sort_clash e s
    | (EReco(l)     , SV _     ) ->
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
            infer env vars v _st; r := `T; all_val << false (* >> *)
        in
        List.iter fn l;
        sort_uvar_set r (if !all_val then _sv else _st)
    | (EReco(_)     , _        ) -> sort_clash e s
    | (EScis        , SV _     )
    | (EScis        , ST       ) -> ()
    | (EScis        , SUni(r)  ) -> sort_uvar_set r _sv; infer env vars e s
    | (EScis        , _        ) -> sort_clash e s
    | (EGoal(str)   , SV _     )
    | (EGoal(str)   , ST       )
    | (EGoal(str)   , SS       ) -> ()
    | (EGoal(str)   , SUni(r)  ) -> sort_uvar_set r _sv; infer env vars e s
    | (EGoal(_)     , _        ) -> sort_clash e s
    | (EAppl(t,u)   , ST       ) -> infer env vars t s; infer env vars u s
    | (EAppl(_,_)   , SUni(r)  ) -> sort_uvar_set r _st; infer env vars e s
    | (EAppl(_,_)   , _        ) -> sort_clash e s
    | (ESequ(t,u)   , ST       ) -> infer env vars t s; infer env vars u s
    | (ESequ(_,_)   , SUni(r)  ) -> sort_uvar_set r _st; infer env vars e s
    | (ESequ(_,_)   , _        ) -> sort_clash e s
    | (EMAbs(arg,t) , ST       ) ->
        let vars = M.add arg.elt (arg.pos, Pos.none SS) vars in
        infer env vars t _st
    | (EMAbs(_,_)   , SUni(r)  ) -> sort_uvar_set r _st; infer env vars e s
    | (EMAbs(_,_)   , _        ) -> sort_clash e s
    | (EName(s,t)   , ST       ) -> infer env vars s _ss; infer env vars t _st
    | (EName(_,_)   , SUni(r)  ) -> sort_uvar_set r _st; infer env vars e s
    | (EName(_,_)   , _        ) -> sort_clash e s
    | (EProj(v,r,_) , ST       ) ->
        begin
          try infer env vars v _sv; r := `V
          with Sort_clash(_,_) ->
            infer env vars v _st; r := `T
        end
    | (EProj(_,_,_) , SUni(r)  ) -> sort_uvar_set r _st; infer env vars e s
    | (EProj(_,_,_) , _        ) -> sort_clash e s
    | (ECase(v,r,l) , ST       ) ->
        begin
          let fn ((_, argo), t) =
            let (x, ao) = Option.default (Pos.none "_", None) argo in
            infer env (M.add x.elt (x.pos, _sv) vars) t _st;
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
    | (ECase(_,_,_) , SUni(r)  ) -> sort_uvar_set r _st; infer env vars e s
    | (ECase(_,_,_) , _        ) -> sort_clash e s
    | (EFixY(s,a,v) , ST       ) -> let vars =
                                      M.add a.elt (a.pos, Pos.none ST) vars
                                    in
                                    infer env vars v _sv
    | (EFixY(_)     , SUni(r)  ) -> sort_uvar_set r _st; infer env vars e _st
    | (EFixY(_)     , _        ) -> sort_clash e s
    | (EPrnt(_)     , ST       ) -> ()
    | (EPrnt(_)     , _        ) -> sort_clash e s
    | (ERepl(t,u,p) , ST       ) -> infer env vars t _st;
                                    infer env vars u _st;
                                    infer env vars p _st
    | (ERepl(t,u,p) , SUni(r)  ) -> sort_uvar_set r _st;
                                    infer env vars t _st;
                                    infer env vars u _st;
                                    infer env vars p _st
    | (ERepl(_,_,_) , _        ) -> sort_clash e s
    | (EDelm(u)     , ST       ) -> infer env vars u _st;
    | (EDelm(u)     , SUni(r)  ) -> sort_uvar_set r _st;
                                    infer env vars u _st;
    | (EDelm(_)     , _        ) -> sort_clash e s
    | (ECoer(u,t,a) , SV _     )
    | (ECoer(u,t,a) , ST       )
    | (ECoer(u,t,a) , SUni(_)  ) -> infer env vars t u; leq u s;
                                    infer env vars a _sp
    | (ECoer(_,t,_) , _        ) -> sort_clash e s
    | (ESuch(u,vs,j,v), SV _   )
    | (ESuch(u,vs,j,v), ST     )
    | (ESuch(u,vs,j,v), SUni(_)) ->
        begin
          let (xo,a) = j in
          let gn x =
            try
              let s = sort_repr env (snd (M.find x.elt vars)) in
              match s.elt with
              | SV _ | SS | SUni(_) -> ()
              | s'                 ->
                  sort_clash (Pos.make x.pos (EVari(x,s))) (Pos.none s')
            with Not_found -> unbound_var x.elt x.pos
          in
          Option.iter gn xo;
          let fn vars (x,s) = M.add x.elt (x.pos, s) vars in
          let vars = List.fold_left fn vars (ne_list_to_list vs) in
          infer env vars a _sp;
          infer env vars v u;
          leq u s
        end
    | (ESuch(_)     ,  _       ) -> sort_clash e s
    | (EPSet(u,_,a) , SV _     )
    | (EPSet(u,_,a) , ST       )
    | (EPSet(u,_,a) , SUni(_)  ) -> infer env vars a u; leq u s;
    | (EPSet(b,d,_) , _        ) -> sort_clash e s
    (* Ordinals. *)
    | (EConv        , SO       ) -> ()
    | (ESucc(o,_)   , SO       ) -> infer env vars o s
    | (EConv        , SUni(r)  )
    | (ESucc(_)     , SUni(r)  ) -> sort_uvar_set r _so; infer env vars e s
    | (EConv        , _        )
    | (ESucc(_)     , _        ) -> sort_clash e s
  in infer env M.empty e s

type boxed = Box : 'a sort * 'a ex loc Bindlib.bindbox -> boxed

let box_set_pos : boxed -> Pos.popt -> boxed = fun (Box(s,e)) pos ->
  Box(s, Bindlib.box_apply (fun e -> {e with pos}) e)

let rec sort_filter : type a b. a sort -> boxed -> a box =
  fun s bx ->
    match (s, bx) with
    | (T, Box(V,e)) -> valu (Bindlib.unbox e).pos e
    | (s, Box(k,e)) ->
        begin
          match Sorts.eq_sort k s with
          | Eq.Eq  -> e
          | Eq.NEq -> Printf.printf "ERROR: %a ≠ %a\n  %a\n%!"
                        Print.sort s Print.sort k Print.ex (Bindlib.unbox e);
                      assert false (* FIXME #11 error management. *)
        end

let to_valu : boxed -> v box = sort_filter V

let to_term : boxed -> t box = fun e ->
  match e with
  | Box(T,e) -> e
  | Box(V,e) -> valu (Bindlib.unbox e).pos e
  | _        -> assert false

let to_stac : boxed -> s box = sort_filter S
let to_prop : boxed -> p box = sort_filter P
let to_ordi : boxed -> o box = sort_filter O

let to_v_or_t : type a. a v_or_t -> boxed -> a box =
  fun vot b ->
    match vot with
    | VoT_V -> to_valu b
    | VoT_T -> to_term b

let add_store : (vvar * tbox) list ref option -> vvar -> tbox -> unit =
  fun store v t ->
    match store with
    | None -> assert false
    | Some ptr -> ptr := (v,t) :: !ptr

let unsugar_expr : env -> raw_ex -> raw_sort -> boxed = fun env e s ->
  infer_sorts env e s;
  let rec unsugar env vars e s =
    log_par "unsug %a : %a" print_raw_expr e print_raw_sort s;
    match (e.elt, (sort_repr env s).elt) with
    | (EVari(x,sx)   , s0       ) when leq_sort env sx s ->
        begin
          log_par "unsug ici 0";
          try box_set_pos (snd (M.find x.elt vars)) e.pos
          with Not_found -> try
            log_par "unsug ici 1";
            let Expr(sx, d) = find_expr x.elt env in
            let bx = Box(sx, Bindlib.box (Pos.make x.pos (HDef(sx,d)))) in
            box_set_pos bx e.pos
          with Not_found ->
            log_par "unsug ici 2";
            let d = find_value x.elt env in
            Box(V, Bindlib.box (Pos.make x.pos (VDef(d))))
        end
    | (EHOAp(f,xs,es), s0      ) ->
        let box = unsugar env vars f xs in
        let rec build_app (Box(se,ex)) args =
          match (se, args) with
          | (F(sa,sb), a::args) ->
             let sa' = sort_from_ast sa in
             let a = sort_filter sa (unsugar env vars a sa') in
             build_app (Box(sb, happ e.pos sa ex a)) args
          | (_       , []     ) -> Box(se,ex)
          | (_       , _      ) -> assert false
        in
        let Box(se,ex) = build_app box es in
        let Sort s = unsugar_sort env s in
        begin
          match Sorts.eq_sort s se with
          | Eq.Eq  -> Box(s, sort_filter s (Box(se,ex)))
          | Eq.NEq ->
             begin
               match (s, s0, se) with
               | (T, _       , V) -> Box(T, valu e.pos ex)
               | (V, SV store, T) ->
                  let v = Bindlib.new_var (mk_free V) "x" in
                  add_store store v ex;
                  Box(V,vari e.pos v)
               | (_, _       , _) -> assert false
             end
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
    | (EFunc(t,a,b) , SP       ) ->
        let a = unsugar env vars a s in
        let b = unsugar env vars b s in
        Box(P, func e.pos t (to_prop a) (to_prop b))
    | (EUnit        , SP       ) -> Box(P, strict_prod e.pos A.empty)
    | (EUnit        , SV _     ) -> Box(V, reco e.pos A.empty)
    | (EUnit        , ST       ) -> Box(T, valu e.pos (reco e.pos A.empty))
    | (EProd(l,str) , SP       ) ->
        let fn (p, a) = (p.elt, (p.pos, to_prop (unsugar env vars a s))) in
        let gn m (k,v) =
          if A.mem k m then assert false;
          A.add k v m
        in
        let m = List.fold_left gn A.empty (List.map fn l) in
        Box(P, (if str then strict_prod else prod) e.pos m)
    | (EDSum(l)     , SP       ) ->
        let fn (p, a) =
          match a with
          | None   -> (p.elt, (p.pos, strict_prod p.pos A.empty))
          | Some a -> (p.elt, (p.pos, to_prop (unsugar env vars a s)))
        in
        let gn m (k,v) =
          if A.mem k m then assert false;
          A.add k v m
        in
        let m = List.fold_left gn A.empty (List.map fn l) in
        Box(P, dsum e.pos m)
    | (EUniv(xs,k,e), SP       ) ->
        let Sort k = unsugar_sort env k in
        let xs = ne_list_to_list xs in
        let rec build vars xs ex =
          match xs with
          | []    -> to_prop (unsugar env vars ex _sp)
          | x::xs -> let fn xk : p box =
                       let xk = (x.pos, Box(k, vari x.pos xk)) in
                       let vars = M.add x.elt xk vars in
                       build vars xs ex
                     in
                     univ ex.pos x k fn
        in
        Box(P, build vars xs e)
    | (EExis(xs,k,e), SP       ) ->
        let Sort k = unsugar_sort env k in
        let xs = ne_list_to_list xs in
        let rec build vars xs ex =
          match xs with
          | []    -> to_prop (unsugar env vars ex _sp)
          | x::xs -> let fn xk : p box =
                       let xk = (x.pos, Box(k, vari x.pos xk)) in
                       let vars = M.add x.elt xk vars in
                       build vars xs ex
                     in
                     exis ex.pos x k fn
        in
        Box(P, build vars xs e)
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
          | None   -> strict_prod e.pos A.empty
          | Some a -> to_prop (unsugar env vars a _sp)
        in
        let c =
          match eq with
          | EEquiv(t,b,u) ->
             let t = to_term (unsugar env vars t _st) in
             let u = to_term (unsugar env vars u _st) in
             equiv t b u
          | ENoBox(v) ->
             let v = to_valu (unsugar env vars v _sv) in
             nobox v
        in
        Box(P, rest e.pos a c)
    | (EImpl(eq,a)  , SP       ) ->
        let a =
          match a with
          | None   -> strict_prod e.pos A.empty
          | Some a -> to_prop (unsugar env vars a _sp)
        in
        let c =
          match eq with
          | EEquiv(t,b,u) ->
             let t = to_term (unsugar env vars t _st) in
             let u = to_term (unsugar env vars u _st) in
             equiv t b u
          | ENoBox(v) ->
             let v = to_valu (unsugar env vars v _sv) in
             nobox v
        in
        Box(P, impl e.pos c a)
    (* Values. *)
    | (ELAbs(args,t), SV _     ) ->
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
              let t = Pos.make e.pos (ELAbs((y,xs),t)) in
              let t = Pos.make e.pos (ELAbs((x,[]),t)) in
              unsugar env vars t _sv
        end
    | (ECons(c,vo)  , SV _     ) ->
        let v =
          match vo with
          | None       -> reco None A.empty
          | Some (v,_) -> to_valu (unsugar env vars v s)
        in
        Box(V, cons e.pos c v)
    | (EReco(l)     , SV _     ) ->
        let fn (p,v,_) = (p.elt, (p.pos, to_valu (unsugar env vars v s))) in
        let gn m (k,v) =
          if A.mem k m then assert false;
          A.add k v m
        in
        let m = List.fold_left gn A.empty (List.map fn l) in
        Box(V, reco e.pos m)
    | (EScis        , SV _     ) -> Box(V, scis e.pos)
    (* Values as terms. *)
    | (ECons(_)     , ST       )
    | (EReco(_)     , ST       ) ->
        let l = ref [] in
        let v = to_valu (unsugar env vars e (_sv_store l)) in
        Box(T, redexes e.pos !l (valu e.pos v))
    | (ELAbs(_,_)   , ST       )
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
    | (ESequ(t,u)   , ST       ) ->
        let t = to_term (unsugar env vars t _st) in
        let u = to_term (unsugar env vars u _st) in
        Box(T, sequ e.pos t u)
    | (EMAbs(arg,t) , ST       ) ->
        let fn x =
          let x = (arg.pos, Box(S, vari arg.pos x)) in
          let vars = M.add arg.elt x vars in
          to_term (unsugar env vars t _st)
        in
        Box(T, mabs e.pos arg fn)
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
          let fn ((c, argo), t) =
            let (x, ao) = Option.default (Pos.none "_", None) argo in
            let f xx =
              let xx = (x.pos, Box(V, vari x.pos xx)) in
              let vars = M.add x.elt xx vars in
              to_term (unsugar env vars t _st)
            in
            (c.elt, (c.pos, x, f))
          in
          let get_pos (p,_,_) = p in
          let gn m (k,v) =
            if A.mem k m then already_matched (Pos.make (get_pos v) k);
            A.add k v m
          in
          let m = List.fold_left gn A.empty (List.map fn l) in
          match !r with
          | `V -> let v = to_valu (unsugar env vars v _sv) in
                  Box(T, case e.pos v m)
          | `T -> let l = ref [] in
                  let v = to_valu (unsugar env vars v (_sv_store l)) in
                  Box(T, redexes e.pos !l (case e.pos v m))
        end
    | (EFixY(s,a,v) , ST       ) ->
        let fn x =
          let x = (a.pos, Box(T, vari a.pos x)) in
          let vars = M.add a.elt x vars in
          to_valu (unsugar env vars v _sv)
        in
        Box(T, fixy e.pos s a fn)
    | (EPrnt(s)     , ST       ) ->
        Box(T, prnt e.pos s)
    | (ERepl(t,u,p) , ST       ) ->
        let t = to_term (unsugar env vars t _st) in
        let u = to_term (unsugar env vars u _st) in
        let p = to_term (unsugar env vars p _st) in
        Box(T, repl e.pos t u p)
    | (EDelm(u)     , ST       ) ->
        let u = to_term (unsugar env vars u _st) in
        Box(T, delm e.pos u)
    (* Type annotations. *)
    | (ECoer(u,v,a) , SV _     ) when leq_sort env u s ->
        let v = to_valu (unsugar env vars v s) in
        let a = to_prop (unsugar env vars a _sp) in
        Box(V, coer e.pos VoT_V v a)
    | (ECoer(u,t,a)   , ST     ) when leq_sort env u s ->
        let t = to_term (unsugar env vars t _st) in
        let a = to_prop (unsugar env vars a _sp) in
        Box(T, coer e.pos VoT_T t a)
    | (ESuch(u,v,j,r), (SV _|ST)) when leq_sort env u s ->
        let xs = map_ne_list (fun (x,s) -> (x, unsugar_sort env s)) v in
        let (var, a) = j in
        let rec build_desc (x,xs) =
          match xs with
          | []               -> let (x, Sort sx) = x in
                                Desc(LastS(sx, x))
          | (y, Sort sy)::xs -> let Desc d = build_desc (x,xs) in
                                Desc(MoreS(sy, y, d))
        in
        let Desc d = build_desc xs in
        let rec build_seq : type a b. a v_or_t -> 'c -> b desc
            -> (b, p ex loc * a ex loc) fseq =
          fun vot vars d ->
            match d with
            | LastS(sx, x)    ->
                let fn xx =
                  let xx = (x.pos, Box(sx, vari x.pos xx)) in
                  let vars = M.add x.elt xx vars in
                  let a = to_prop (unsugar env vars a _sp) in
                  let e = to_v_or_t vot (unsugar env vars r s) in
                  Bindlib.box_pair a e
                in
                FLast(sx, x, fn)
            | MoreS(sy, y, d) ->
                let fn yy =
                  let yy = (y.pos, Box(sy, vari y.pos yy)) in
                  let vars = M.add y.elt yy vars in
                  build_seq vot vars d
                in
                FMore(sy, y, fn)
        in
        let sv =
          match var with
          | None   -> sv_none
          | Some x ->
              begin
                match snd (M.find x.elt vars) with
                | Box(V,v) -> sv_valu v
                | Box(S,s) -> sv_stac s
                | Box(_,_) -> assert false (* should not happen *)
              end
        in
        begin
          match s.elt with
          | SV _ -> Box(V, such e.pos VoT_V d sv (build_seq VoT_V vars d))
          | ST   -> Box(T, such e.pos VoT_T d sv (build_seq VoT_T vars d))
          | _    -> assert false (* should not happen *)
        end
    (* Ordinals. *)
    | (EPSet(u,l,a) , SV _     ) when leq_sort env u s
                                 -> let v = to_valu (unsugar env vars a s) in
                                    Box(V, pset e.pos l VoT_V v)
    | (EPSet(u,l,a) , ST       ) when leq_sort env u s
                                 -> let t = to_term (unsugar env vars a s) in
                                    Box(T, pset e.pos l VoT_T t)
    | (EConv        , SO       ) -> Box(O, conv e.pos)
    | (ESucc(o,n)   , SO       ) ->
        assert (n >= 0);
        let o = to_ordi (unsugar env vars o _so) in
        let rec fn n =
          if n = 0 then o else succ e.pos (fn (n-1)) in
        Box(O, fn n)
    | (EGoal(str)   , SV _      ) -> Box(V, goal e.pos V str)
    | (EGoal(str)   , ST       ) -> Box(T, to_term (Box(V, goal e.pos V str)))
    | (EGoal(str)   , SS       ) -> Box(S, goal e.pos S str)
    | (_, SV store) when store <> None ->
       let v = Bindlib.new_var (mk_free V) "x" in
       let t = to_term (unsugar env vars e (Pos.make s.pos ST)) in
       add_store store v t;
       Box(V,vari e.pos v)
    | (_            , _        ) -> assert false
  in
  unsugar env M.empty e s

type toplevel =
  | Sort_def of strloc * raw_sort
  | Expr_def of strloc * raw_sort * raw_ex
  | Valu_def of strloc * raw_ex * raw_ex
  | Chck_sub of raw_ex * bool * raw_ex
  | Include  of string list
  | Def_list of toplevel list
  | Glbl_set of set_param

let evari _loc x = Pos.make _loc (EVari(x, new_sort_uvar None))

let sort_def : strloc -> raw_sort -> toplevel = fun id s ->
  Sort_def(id,s)

let expr_def : strloc -> (strloc * raw_sort option) list -> raw_sort option
               -> raw_ex -> toplevel = fun id args s e ->
  let s = sort_from_opt s in
  let args = List.map (fun (id,so) -> (id, sort_from_opt so)) args in
  let f (id,s) e = Pos.none (EHOFn(id,s,e)) in
  let e = List.fold_right f args e in
  let f (_ ,a) s = Pos.none (SFun(a,s)) in
  let s = List.fold_right f args s in
  Expr_def(id,s,e)

let type_def : Pos.pos -> [`Non | `Rec | `CoRec] -> strloc
               -> (strloc * raw_sort option) list
               -> raw_ex -> toplevel = fun _loc r id args e ->
  let e1 =
    match r with
    | `Non   -> e
    | `Rec   -> in_pos _loc (EFixM(Pos.none EConv, id, e))
    | `CoRec -> in_pos _loc (EFixN(Pos.none EConv, id, e))
  in
  let d1 = expr_def id args (Some (Pos.none SP)) e1 in
  if r = `Non then d1 else
    begin
      let id2 = Pos.make id.pos (id.elt ^ "#") in
      let s = evari None (Pos.none "s#") in
      let e2 =
        match r with
        | `Non   -> assert false
        | `Rec   -> in_pos _loc (EFixM(s, id, e))
        | `CoRec -> in_pos _loc (EFixN(s, id, e))
      in
      let args = (Pos.none "s#", Some (Pos.none SO)) :: args in
      let d2 = expr_def id2 args (Some (Pos.none SP)) e2 in
      Def_list [d1;d2]
    end

type rec_t = [ `Non | `Rec | `Unsafe ]

let val_def : rec_t -> strloc -> raw_ex -> raw_ex -> toplevel = fun r id a t ->
  let t = if r = `Non then t else Pos.make t.pos (EFixY(r=`Rec,id, t)) in
  Valu_def(id, a, t)

let check_sub : raw_ex -> bool -> raw_ex -> toplevel = fun a r b ->
  Chck_sub(a,r,b)

let include_file : string list -> toplevel = fun path ->
  Include(path)

(** syntactic sugars *)

let tuple_type _loc bs =
  let fn i a = (Pos.none (string_of_int (i+1)), a) in
  in_pos _loc (EProd(List.mapi fn bs, true))

let tuple_term _loc ts =
  let fn i t = (Pos.none (string_of_int (i+1)), t, ref `T) in
  in_pos _loc (EReco(List.mapi fn ts))

let record _loc fs =
  let fn (l, ao) =
    let a = Option.default (evari l.pos l) ao in
    (l, a, ref `T)
  in
  in_pos _loc (EReco(List.map fn fs))

let erest a l =
  List.fold_left (fun a x ->
      Pos.none (ERest(Some a,ENoBox(evari x.pos x)))) a l

let eimpl a l =
  List.fold_left (fun a x ->
      Pos.none (EImpl(ENoBox(evari None x), Some a))) a l

let euniv _loc x xs s a =
  let s = match s with Some s -> s | None -> new_sort_uvar (Some x) in
  let a = match s.elt with SV _ -> eimpl a (x::xs) | _ -> a in
  in_pos _loc (EUniv((x,xs), s, a))

let eexis _loc x xs s a =
  let s = match s with Some s -> s | None -> new_sort_uvar (Some x) in
  let a = match s.elt with SV _ -> erest a (x::xs) | _ -> a in
  in_pos _loc (EExis((x,xs), s, a))

let euniv_in _loc x xs a b =
  let p x = Pos.in_pos _loc x in
  let c = List.fold_right (fun x c ->
    (* FIXME #21: notation for partial dependant product ? *)
    p (EFunc(Totality.Tot, p (EMemb(evari (Some _loc) x, a)), c))) (x::xs) b
  in
  p (EUniv((x,xs),p sv,c))

let eexis_in _loc x xs a b =
  let p x = Pos.in_pos _loc x in
  let l = List.map (fun x -> p (EMemb(evari (Some _loc) x, a))) (x::xs) in
  let c = tuple_type _loc (l @ [b]) in
  (* Alternatives, only with pair
  let c = List.fold_right (fun x c ->
    tuple_type _loc [p (EMemb(p (EVari(x,[])), a)); c]) (x::xs) b
  in
  *)
  p (EExis((x,xs),p sv,c))

let esett _loc x a =
  let a = Pos.none (EMemb(evari x.pos x, a)) in
  in_pos _loc (EExis((x,[]), _sv, a))

(* "let ... such that ..." *)
let esuch _loc vs x a u =
  let fn (x,so) =
    (x, match so with Some s -> s | None -> new_sort_uvar (Some x))
  in
  let x = if x.elt = "_" then None else Some x in
  let vs = List.map fn vs in
  let vs = (List.hd vs, List.tl vs) in
  in_pos _loc (ESuch(new_sort_uvar None,vs,(x,a),u))

(* The built it type of booleans. *)
let p_bool _loc =
  Pos.make _loc (EDSum [(Pos.none "true", None) ; (Pos.none "false", None)])

(* "if c then t else e" := "case t:bool of { Tru[_] -> t | Fls[_] -> e }" *)
let if_then_else _loc c t e =
  let e = match e with Some e -> e | None -> Pos.none EUnit in
  let no_arg c t = ((Pos.none c, None), t) in
  let pats = [ no_arg "true" t ; no_arg "false" e ] in
  Pos.in_pos _loc (ECase(c, ref `T, pats))

(* "let x : a = t in u" := "(fun (x:a) -> u) (t:a)" *)
let let_binding _loc r arg t u =
  match arg with
  | `LetArgVar(id,ao) ->
     let t = if r = `Non then t else Pos.make t.pos (EFixY(r=`Rec,id, t)) in
     let t =
        match ao with
        | None   -> t
        | Some a -> Pos.make t.pos (ECoer(new_sort_uvar None,t,a))
      in
      in_pos _loc (EAppl(Pos.make u.pos (ELAbs(((id, ao), []), u)), t))
  | `LetArgRec(fs)    ->
      if r <> `Non then Earley.give_up (); (* "let rec" is meaningless here. *)
      let xs = List.map snd fs in
      let u = Pos.make u.pos (ELAbs((List.hd xs, List.tl xs), u)) in
      let x = Pos.none "$rec$" in
      let fn u (l,_) =
        let pr = Pos.none (EProj(evari None x, ref `T,  l)) in
        Pos.make u.pos (EAppl(u, pr))
      in
      let u = List.fold_left fn u fs in
      in_pos _loc (EAppl(Pos.make u.pos (ELAbs(((x, None), []), u)), t))
  | `LetArgTup(fs)    ->
      if r <> `Non then Earley.give_up (); (* "let rec" is meaningless here. *)
      let u = Pos.make u.pos (ELAbs((List.hd fs, List.tl fs), u)) in
      let x = Pos.none "$tup$" in
      let is = List.mapi (fun i _ -> Pos.none (string_of_int (i+1))) fs in
      let fn u l =
        let pr = Pos.none (EProj(evari None x, ref `T,  l)) in
        Pos.make u.pos (EAppl(u, pr))
      in
      let u = List.fold_left fn u is in
      in_pos _loc (EAppl(Pos.make u.pos (ELAbs(((x, None), []), u)), t))

let pattern_matching _loc t ps =
  let fn ((c,pat), t) =
    let (pat, t) =
      match pat with
      | None                    -> (None        , t)
      | Some(`LetArgVar(id,ao)) -> (Some (id,ao), t)
      | Some(`LetArgRec(fs)   ) ->
          let xs = List.map snd fs in
          let t = Pos.make t.pos (ELAbs((List.hd xs, List.tl xs), t)) in
          let x = Pos.none "$rec$" in
          let fn t (l,_) =
            let pr = Pos.none (EProj(evari None x, ref `T,  l)) in
            Pos.make t.pos (EAppl(t, pr))
          in
          (Some (x, None), List.fold_left fn t fs)
      | Some(`LetArgTup(fs)   ) ->
          let t = Pos.make t.pos (ELAbs((List.hd fs, List.tl fs), t)) in
          let x = Pos.none "$tup$" in
          let is = List.mapi (fun i _ -> Pos.none (string_of_int (i+1))) fs in
          let fn t l =
            let pr = Pos.none (EProj(evari None x, ref `T,  l)) in
            Pos.make t.pos (EAppl(t, pr))
          in
          (Some (x, None), List.fold_left fn t is)
    in ((c,pat), t)
  in
  let ps = List.map fn ps in
  in_pos _loc (ECase(t, ref `T, ps))

(* (strloc * (strloc * raw_ex option) option) * raw_ex *)

(* Boolean values. *)
let v_bool _loc b =
  let b = ECons(Pos.none (if b then "true" else "false"), None) in
  Pos.in_pos _loc (ECoer(_sv, Pos.in_pos _loc b, p_bool None))

(* Empty list. *)
let v_nil _loc =
  Pos.in_pos _loc (ECons(Pos.in_pos _loc "Nil", None))

(* Cons on lists. *)
let v_cons _loc t u =
  let args = [ (Pos.none "hd", t, ref `T) ; (Pos.none "tl", u, ref `T) ] in
  let arg = (Pos.none (EReco(args)), ref `T) in
  Pos.in_pos _loc (ECons(Pos.none "Cons", Some arg))

(* "deduce a" := "{} : a" *)
let deduce _loc a =
  Pos.in_pos _loc (ECoer(_sv, Pos.none (EReco []), a))

(* "show a using p" := "p : a" *)
let show_using _loc a t =
  Pos.in_pos _loc (ECoer(new_sort_uvar None, t, a))

(* "use a" := "a" *)
let use _loc t =
  t

(* "qed" := "{}" *)
let qed _loc =
  Pos.in_pos _loc (EReco([]))

(* "from a; p" := "let _ = p : a in {}" *)
let showing _loc a p =
  let_binding _loc `Non (`LetArgVar(Pos.none "",None))
    (Pos.in_pos _loc (ECoer(new_sort_uvar None, p,a)))
    (Pos.in_pos _loc (EReco []))

let suppose _loc props t =
  let args = List.map (fun p -> (Pos.none "_", Some p)) props in
  in_pos _loc (ELAbs((List.hd args, List.tl args),t))

let assume _loc t u =
  in_pos _loc (ECase(t, ref `T, [((Pos.none "false", None), in_pos _loc EUnit);
                                 ((Pos.none "true" , None), u)]))
