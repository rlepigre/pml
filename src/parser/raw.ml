(** Parser level abstract syntax tree. This module defines the low level (raw)
    AST for the language. This is where most syntactic sugars are applied. *)

open Pos
open Pacomb
open Output
open Extra
open Sorts
open Ast
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
let _sv = none sv
let _sv_store l = none (SV (Some l))
let _st = none ST
let _ss = none SS
let _sp = none SP
let _so = none SO

let rec sort_from_ast : type a. a sort -> raw_sort = function
  | V      -> _sv
  | T      -> _st
  | S      -> _ss
  | P      -> _sp
  | O      -> _so
  | F(s,k) -> none (SFun(sort_from_ast s, sort_from_ast k))

let new_sort_uvar : strloc option -> raw_sort =
  let i = ref (-1) in
  fun x ->
    incr i;
    log_par "?%i is introduced" !i;
    none (SUni (!i, x, ref None))

let sort_uvar_set : suvar -> raw_sort -> unit =
  fun (i,_,r) v ->
    let open Timed in
    assert(!r = None);
    log_par "?%i := %a" i print_raw_sort v;
    r := Some v

let sort_from_opt : raw_sort option -> raw_sort = fun so ->
  match so with
  | None   -> new_sort_uvar None
  | Some s -> s

let rec sort_repr : raw_sort -> raw_sort = fun s ->
  match s.elt with
  | SUni(_,_,{contents = Some s}) -> sort_repr s
  | SVar(x)                       ->
      begin
        try
          let Sort s = find_sort x in
          sort_from_ast s
        with Not_found -> s
      end
  | _                             -> s

exception Unbound_sort of string * pos option
let unbound_sort : string -> pos option -> 'a =
  fun s p -> raise (Unbound_sort(s,p))

let rec unsugar_sort : raw_sort -> any_sort = fun s ->
  match (sort_repr s).elt with
  | SV _        -> Sort V
  | ST          -> Sort T
  | SS          -> Sort S
  | SP          -> Sort P
  | SO          -> Sort O
  | SFun(o1,o2) ->
      begin
        match (unsugar_sort o1, unsugar_sort o2) with
        | (Sort o1, Sort o2) -> Sort (F(o1,o2))
      end
  | SVar(x)     ->
      begin
        try find_sort x with Not_found -> unbound_sort x s.pos
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

  | EFunc of Effect.t * raw_ex * raw_ex * laz
  | EProd of (strloc * raw_ex) list * bool
  | EUnit (* Empty record as a type or a term *)
  | EDSum of (strloc * raw_ex option) list
  | EUniv of strloc ne_list * raw_sort * raw_ex
  | EExis of strloc ne_list * raw_sort * raw_ex
  | EFixM of raw_sort * raw_ex * strloc * raw_ex
  | EFixN of raw_sort * raw_ex * strloc * raw_ex
  | EMemb of raw_ex * raw_ex
  | ERest of raw_ex option * raw_cond
  | EImpl of raw_cond * raw_ex option

  | ELAbs of (strloc * raw_ex option) ne_list * raw_ex * laz
  | ECons of strloc * (raw_ex * flag) option
  | EReco of (strloc * raw_ex * flag) list
  | EScis
  | EAppl of raw_ex * raw_ex * laz
  | ESequ of raw_ex * raw_ex
  | EMAbs of strloc * raw_ex
  | EName of raw_ex * raw_ex
  | EProj of raw_ex * flag * strloc
  | ECase of raw_ex * flag * patt_ex list
  | EFixY of strloc * raw_ex
  | EPrnt of string
  | ERepl of raw_ex * raw_ex * raw_ex option
  | EDelm of raw_ex
  | ECoer of raw_sort * raw_ex * raw_ex
  | ESuch of raw_sort * (strloc * raw_sort) ne_list
                      * (strloc option * raw_ex) * raw_ex
  | EPSet of raw_sort * set_param * raw_ex
  | EInfx of raw_ex * float (* for parsing *)
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
    | EFunc(t,a,b,l)-> Printf.fprintf ch "EFunc(%a,%a,%a,%b)"
                                      print a Print.arrow t print b (l = Lazy)
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
    | EFixM(s,o,x,a)-> Printf.fprintf ch "EFixM(%a,%a,%S,%a)"
                         print_raw_sort s print o x.elt print a
    | EFixN(s,o,x,a)-> Printf.fprintf ch "EFixN(%a,%a,%S,%a)"
                         print_raw_sort s print o x.elt print a
    | EMemb(t,a)    -> Printf.fprintf ch "EMemb(%a,%a)" print t print a
    | ERest(a,eq)   -> Printf.fprintf ch "ERest(%a,%a)" aux_opt a aux_eq eq
    | EImpl(eq,a)   -> Printf.fprintf ch "EImpl(%a,%a)" aux_opt a aux_eq eq
    | ELAbs(ls,t,l) -> Printf.fprintf ch "ELAbs([%a],%a,%b)"
                         (print_list aux_arg "; ")
                         (ne_list_to_list ls) print t (l = Lazy)
    | ECons(c,ao)   -> Printf.fprintf ch "ECons(%S,%a)" c.elt aux_cons ao
    | EReco(l)      -> Printf.fprintf ch "EReco([%a])"
                         (print_list aux_rec "; ") l
    | EScis         -> Printf.fprintf ch "EScis"
    | EAppl(t,u,l)  -> Printf.fprintf ch "EAppl(%a,%a,%b)" print t print u (l = Lazy)
    | ESequ(t,u)    -> Printf.fprintf ch "ESequ(%a,%a)" print t print u
    | EMAbs(arg,t)  -> Printf.fprintf ch "EMAbs(%a,%a)" aux_var arg print t
    | EName(s,t)    -> Printf.fprintf ch "EName(%a,%a)" print s print t
    | EProj(v,_,l)  -> Printf.fprintf ch "EProj(%a,%S)" print v l.elt
    | ECase(v,_,l)  -> Printf.fprintf ch "ECase(%a,[%a])" print v
                         (print_list aux_patt "; ") l
    | EFixY(a,t)    -> Printf.fprintf ch "EFixY(%a,%a)" aux_var a print t
    | EPrnt(s)      -> Printf.fprintf ch "EPrnt(%S)" s
    | ERepl(t,u,p)  -> Printf.fprintf ch "ERepl(%a,%a,%a)"
                         print t print u aux_opt p
    | EDelm(u)      -> Printf.fprintf ch "EDelm(%a)" print u
    | ECoer(_,t,a)  -> Printf.fprintf ch "ECoer(%a,%a)" print t print a
    | ESuch(_,v,j,u)-> let x = Option.default (none "_") (fst j) in
                       Printf.fprintf ch "ESuch(%a,%s,%a,%a)"
                         (print_list aux_sort ", ") (ne_list_to_list v)
                         x.elt print (snd j) print u
    | EInfx(t,p)    -> Printf.fprintf ch "EInfx(%a,%f)" print t p
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

exception Unbound_variable of string * pos option
let unbound_var : string -> pos option -> 'a =
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

let rec leq_sort : ?evar:bool -> raw_sort -> raw_sort -> bool =
  fun ?(evar=false) s1 s2 ->
    log_par "leq_sort %a %a" print_raw_sort s1 print_raw_sort s2;
    let res =
      match ((sort_repr s1).elt, (sort_repr s2).elt) with
      | (SV _       , SV _       ) -> true
      | (ST         , ST         ) -> true
      | (SV _       , ST         ) -> true
      | (SS         , SS         ) -> true
      | (SP         , SP         ) -> true
      | (SO         , SO         ) -> true
      | (SV _       , SP         ) when evar -> true
      | (ST         , SP         ) when evar -> true
      | (SFun(s1,s2), SFun(k1,k2)) -> leq_sort k1 s1 && leq_sort s2 k2
      | (SUni(r1)   , SUni(r2)   ) -> if r1 != r2 then sort_uvar_set r1 s2;
                                      true
      | (SUni(r)    , _          ) -> sort_uvar_set r s2; true
      | (_          , SUni(r)    ) -> sort_uvar_set r s1; true
      | (_          , _          ) -> false
    in log_par "ok"; res

let infer_sorts : raw_ex -> raw_sort -> unit = fun e s ->
  let open Timed in
  let rec infer vars e s =
    log_par "infer %a : %a" print_raw_expr e print_raw_sort s;
    let leq  u s = if not (leq_sort u s) then sort_clash e s in
    let leqv u s = if not (leq_sort ~evar:true u s) then sort_clash e s in
    match (e.elt, (sort_repr s).elt) with
    | (EVari(x,sx)     , _        ) ->
        begin
          try
            let sy =
              try snd (M.find x.elt vars) with Not_found ->
                let Expr(k,d) = find_expr x.elt in
                sort_from_ast k
            in
            leq sy sx; leqv sx s
          with Not_found ->
            try
              ignore (find_value x.elt);
              leq _sv sx; leqv sx s
            with Not_found ->
              unbound_var x.elt x.pos
         end
    | (EHOAp(e,sx,es), _        ) ->
         let nb_args = List.length es in
         infer vars e sx;
         let rec decompose acc nb s =
           let s = sort_repr s in
           match (nb, s.elt) with
           | (0, _        ) -> (List.rev acc, s)
           | (n, SFun(a,b)) -> decompose (a::acc) (n-1) b
           | (n, SUni(r)  ) ->
              let a = new_sort_uvar None in
              let b = new_sort_uvar None in
              sort_uvar_set r (make s.pos (SFun(a,b)));
              decompose (a::acc) (n-1) b
           | (_, _        ) -> too_many_args e
         in
         let (ss, sx) = decompose [] nb_args sx in
         let rec infer_args args ss =
           match (args, ss) with
           | ([]     , []   ) -> ()
           | (a::args, s::ss) -> infer vars a s; infer_args args ss
           | _                -> assert false
         in
         infer_args es ss;
         leq sx s
    | (EInfx(t,_)   , ST       )
    | (EInfx(t,_)   , SP       ) -> infer vars t _st
    | (EInfx _      , SUni(r)  ) -> sort_uvar_set r _st; infer vars e s
    | (EInfx _      , _        ) -> sort_clash e s
    | (EHOFn(x,k,f) , SFun(a,b)) -> leq a k;
                                    let vars = M.add x.elt (x.pos, k) vars in
                                    infer vars f b
    | (EHOFn(_,_,_) , SUni(r)  ) -> let a = new_sort_uvar None in
                                    let b = new_sort_uvar None in
                                    sort_uvar_set r (none (SFun(a,b)));
                                    infer vars e s
    | (EHOFn(_,_,_) , _        ) -> sort_clash e s
    (* Propositions. *)
    | (EFunc(_,a,b,_), SP       ) -> infer vars a _sp; infer vars b _sp
    | (EFunc(_,_,_,_), SUni(r)  ) -> sort_uvar_set r _sp; infer vars e s
    | (EFunc(_,_,_,_), _        ) -> sort_clash e s
    | (EUnit        , SP       )
    | (EUnit        , SV _     )
    | (EUnit        , ST       ) -> ()
    | (EUnit        , SUni(r)  ) -> sort_uvar_set r _sv; (* arbitrary *)
                                    infer vars e s
    | (EUnit        , _        ) -> sort_clash e s
    | (EDSum(l)     , SP       ) -> let fn (_, a) =
                                      match a with
                                      | None   -> ()
                                      | Some a -> infer vars a _sp
                                    in List.iter fn l
    | (EProd(l,_)   , SP       ) -> let fn (_, a) =
                                      infer vars a _sp
                                    in List.iter fn l
    | (EDSum(_)     , SUni(r)  )
    | (EProd(_,_)   , SUni(r)  ) -> sort_uvar_set r _sp;
                                    infer vars e s
    | (EDSum(_)     , _        )
    | (EProd(_,_)   , _        ) -> sort_clash e s
    | (EUniv(xs,k,e), SP       )
    | (EExis(xs,k,e), SP       ) -> let fn vars x =
                                      M.add x.elt (x.pos, k) vars
                                    in
                                    let xs = ne_list_to_list xs in
                                    let vars = List.fold_left fn vars xs in
                                    infer vars e s
    | (EUniv(_,_,_) , SUni(r)  )
    | (EExis(_,_,_) , SUni(r)  ) -> sort_uvar_set r _sp;
                                    infer vars e s
    | (EUniv(_,_,_) , _        )
    | (EExis(_,_,_) , _        ) -> sort_clash e s
    | (EFixM(k,o,x,e) , _      )
    | (EFixN(k,o,x,e) , _      ) -> leq k s;
                                    infer vars o _so;
                                    let vars = M.add x.elt (x.pos,k) vars in
                                    infer vars e k
    | (EMemb(t,a)   , SP       ) -> infer vars t _st; infer vars a _sp
    | (EMemb(t,a)   , SUni(r)  ) -> sort_uvar_set r _sp; infer vars e s
    | (EMemb(_,_)   , _        ) -> sort_clash e s
    | (ERest(a,eq)  , SP       ) ->
       begin
         match eq with
         | EEquiv(t,_,u) -> infer vars t _st; infer vars u _st
         | ENoBox(v)     -> infer vars v _sv
       end;
       begin
         match a with
         | None   -> ()
         | Some a -> infer vars a _sp
       end
    | (EImpl(eq,a)  , SP       ) ->
       begin
         match eq with
         | EEquiv(t,_,u) -> infer vars t _st; infer vars u _st
         | ENoBox(v)     -> infer vars v _sv
       end;
       begin
         match a with
         | None   -> ()
         | Some a -> infer vars a _sp
       end
    | (ERest(_,_)   , SUni(r)  ) -> sort_uvar_set r _sp; infer vars e s
    | (ERest(_,_)   , _        ) -> sort_clash e s
    | (EImpl(_,_)   , SUni(r)  ) -> sort_uvar_set r _sp; infer vars e s
    | (EImpl(_,_)   , _        ) -> sort_clash e s
    (* Terms / Values. *)
    | (ELAbs(args,t,_), SV _   )
    | (ELAbs(args,t,_), ST     ) ->
        begin
          let fn vs (x, ao) =
            begin
              match ao with
              | None   -> ()
              | Some a -> infer vars a _sp
            end;
            M.add x.elt (x.pos, _sv) vs
          in
          let vars = List.fold_left fn vars (ne_list_to_list args) in
          infer vars t _st
        end
    | (ELAbs(_,_,_) , SUni(r)  ) -> sort_uvar_set r _sv; infer vars e s
    | (ELAbs(_,_,_) , _        ) -> sort_clash e s
    | (ECons(_,vo)  , SV _     ) ->
        begin
          match vo with
          | None       -> ()
          | Some (v,r) -> infer vars v _sv; r := `V
        end
    | (ECons(_,vo)  , ST       ) ->
        begin
          match vo with
          | None       -> ()
          | Some (v,r) ->
              begin
                let tm = Time.save () in
                try infer vars v _sv; r := `V
                with Sort_clash(_,_) ->
                  Time.rollback tm; infer vars v _st; r := `T
              end
        end
    | (ECons(_,vo)  , SUni(r)  ) ->
        begin
          match vo with
          | None       -> sort_uvar_set r _sv
          | Some (v,f) ->
              begin
                let tm = Time.save () in
                try infer vars v _sv; f := `V; sort_uvar_set r _sv
                with Sort_clash(_,_) ->
                  Time.rollback tm;
                  infer vars v _st; f := `T; sort_uvar_set r _st
              end
        end
    | (ECons(_,_)   , _        ) -> sort_clash e s
    | (EReco(l)     , SV _     ) ->
        let fn (_,v,r) = infer vars v _sv; r := `V in
        List.iter fn l
    | (EReco(l)     , ST       ) ->
        let fn (_,v,r) =
          let tm = Time.save () in
          try infer vars v _sv; r := `V
          with Sort_clash(_,_) ->
            Time.rollback tm;
            infer vars v _st; r := `T
        in
        List.iter fn l
    | (EReco(l)     , SUni(r)  ) ->
        let all_val = ref true in
        let fn (_,v,r) =
          let tm = Time.save () in
          try infer vars v _sv; r := `V
          with Sort_clash(_,_) ->
            Time.rollback tm;
            infer vars v _st; r := `T; all_val << false (* >> *)
        in
        List.iter fn l;
        sort_uvar_set r (if !all_val then _sv else _st)
    | (EReco(_)     , _        ) -> sort_clash e s
    | (EScis        , SV _     )
    | (EScis        , ST       ) -> ()
    | (EScis        , SUni(r)  ) -> sort_uvar_set r _sv; infer vars e s
    | (EScis        , _        ) -> sort_clash e s
    | (EGoal(str)   , SV _     )
    | (EGoal(str)   , ST       )
    | (EGoal(str)   , SS       ) -> ()
    | (EGoal(str)   , SUni(r)  ) -> sort_uvar_set r _sv; infer vars e s
    | (EGoal(_)     , _        ) -> sort_clash e s
    | (EAppl(t,u,_) , ST       ) -> infer vars t s; infer vars u s
    | (EAppl(t,u,_) , SP       ) -> infer vars t _st; infer vars u _st
    | (EAppl(_,_,_) , SUni(r)  ) -> sort_uvar_set r _st; infer vars e s
    | (EAppl(_,_,_) , _        ) -> sort_clash e s
    | (ESequ(t,u)   , ST       ) -> infer vars t s; infer vars u s
    | (ESequ(_,_)   , SUni(r)  ) -> sort_uvar_set r _st; infer vars e s
    | (ESequ(_,_)   , _        ) -> sort_clash e s
    | (EMAbs(arg,t) , ST       ) ->
        let vars = M.add arg.elt (arg.pos, none SS) vars in
        infer vars t _st
    | (EMAbs(_,_)   , SUni(r)  ) -> sort_uvar_set r _st; infer vars e s
    | (EMAbs(_,_)   , _        ) -> sort_clash e s
    | (EName(s,t)   , ST       ) -> infer vars s _ss; infer vars t _st
    | (EName(_,_)   , SUni(r)  ) -> sort_uvar_set r _st; infer vars e s
    | (EName(_,_)   , _        ) -> sort_clash e s
    | (EProj(v,r,_) , ST       ) ->
        begin
          try infer vars v _sv; r := `V
          with Sort_clash(_,_) ->
            infer vars v _st; r := `T
        end
    | (EProj(_,_,_) , SUni(r)  ) -> sort_uvar_set r _st; infer vars e s
    | (EProj(_,_,_) , _        ) -> sort_clash e s
    | (ECase(v,r,l) , ST       ) ->
        begin
          let fn ((_, argo), t) =
            let (x, ao) = Option.default (none "_", None) argo in
            infer (M.add x.elt (x.pos, _sv) vars) t _st;
            match ao with
            | None   -> ()
            | Some a -> infer vars a _sp
          in
          List.iter fn l;
          let tm = Time.save () in
          try infer vars v _sv; r := `V
          with Sort_clash(_,_) ->
            Time.rollback tm;
            infer vars v _st; r := `T
        end
    | (ECase(_,_,_) , SUni(r)  ) -> sort_uvar_set r _st; infer vars e s
    | (ECase(_,_,_) , _        ) -> sort_clash e s
    | (EFixY(a,v)   , ST       ) -> let vars =
                                      M.add a.elt (a.pos, none ST) vars
                                    in
                                    infer vars v _sv
    | (EFixY(_)     , SUni(r)  ) -> sort_uvar_set r _st; infer vars e _st
    | (EFixY(_)     , _        ) -> sort_clash e s
    | (EPrnt(_)     , ST       ) -> ()
    | (EPrnt(_)     , _        ) -> sort_clash e s
    | (ERepl(t,u,p) , ST       ) -> infer vars t _st;
                                    infer vars u _st;
                                    begin
                                      match p with
                                      | None -> ()
                                      | Some p ->  infer vars p _st;
                                    end
    | (ERepl(t,u,p) , SUni(r)  ) -> sort_uvar_set r _st;
                                    infer vars t _st;
                                    infer vars u _st;
                                    begin
                                      match p with
                                      | None -> ()
                                      | Some p ->  infer vars p _st;
                                    end
    | (ERepl(_,_,_) , _        ) -> sort_clash e s
    | (EDelm(u)     , ST       ) -> infer vars u _st;
    | (EDelm(u)     , SUni(r)  ) -> sort_uvar_set r _st;
                                    infer vars u _st;
    | (EDelm(_)     , _        ) -> sort_clash e s
    | (ECoer(u,t,a) , SV _     )
    | (ECoer(u,t,a) , ST       )
    | (ECoer(u,t,a) , SUni(_)  ) -> infer vars t u; leq u s;
                                    infer vars a _sp
    | (ECoer(_,t,_) , _        ) -> sort_clash e s
    | (ESuch(u,vs,j,v), SV _   )
    | (ESuch(u,vs,j,v), ST     )
    | (ESuch(u,vs,j,v), SUni(_)) ->
        begin
          let (xo,a) = j in
          let gn x =
            try
              let s = sort_repr (snd (M.find x.elt vars)) in
              match s.elt with
              | SV _ | SS | SUni(_) -> ()
              | s'                 ->
                  sort_clash (make x.pos (EVari(x,s))) (none s')
            with Not_found ->
              try
                ignore (find_value x.elt)
              with Not_found ->
                unbound_var x.elt x.pos
          in
          Option.iter gn xo;
          let fn vars (x,s) = M.add x.elt (x.pos, s) vars in
          let vars = List.fold_left fn vars (ne_list_to_list vs) in
          infer vars a _sp;
          infer vars v u;
          leq u s
        end
    | (ESuch(_)     ,  _       ) -> sort_clash e s
    | (EPSet(u,_,a) , SV _     )
    | (EPSet(u,_,a) , ST       )
    | (EPSet(u,_,a) , SUni(_)  ) -> infer vars a u; leq u s;
    | (EPSet(b,d,_) , _        ) -> sort_clash e s
    (* Ordinals. *)
    | (EConv        , SO       ) -> ()
    | (ESucc(o,_)   , SO       ) -> infer vars o s
    | (EConv        , SUni(r)  )
    | (ESucc(_)     , SUni(r)  ) -> sort_uvar_set r _so; infer vars e s
    | (EConv        , _        )
    | (ESucc(_)     , _        ) -> sort_clash e s
  in infer M.empty e s

type boxed = Box : 'a sort * 'a ex loc Bindlib.box -> boxed

let box_set_pos : boxed -> popt -> boxed = fun (Box(s,e)) pos ->
  Box(s, Bindlib.box_apply (fun e -> {e with pos}) e)

let sort_filter : type a. a sort -> boxed -> a ebox =
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

let to_valu : boxed -> vbox = sort_filter V

let to_term : boxed -> tbox = fun e ->
  match e with
  | Box(T,e) -> e
  | Box(V,e) -> valu (Bindlib.unbox e).pos e
  | _        -> assert false

let to_stac : boxed -> sbox = sort_filter S
let to_prop : boxed -> pbox = sort_filter P
let to_ordi : boxed -> obox = sort_filter O

let to_v_or_t : type a. a v_or_t -> boxed -> a ebox =
  fun vot b ->
    match vot with
    | VoT_V -> to_valu b
    | VoT_T -> to_term b

let add_store : (vvar * tbox) list ref option -> vvar -> tbox -> unit =
  fun store v t ->
    match store with
    | None -> assert false
    | Some ptr -> ptr := (v,t) :: !ptr

let rec end_by_prop : raw_sort -> unit = fun s ->
  match (sort_repr s).elt with
  | SP | ST | SS | SO | SV _ -> ()
  | SVar _ -> assert false
  | SUni(v) -> sort_uvar_set v (none SP)
  | SFun(_,s) -> end_by_prop s

let unsugar_expr : raw_ex -> raw_sort -> boxed = fun e s ->
  infer_sorts e s;
  let rec unsugar env vars e s =
    log_par "unsug %a : %a" print_raw_expr e print_raw_sort s;
    match (e.elt, (sort_repr s).elt) with
    | (EVari(x,sx)   , s0       ) when leq_sort ~evar:true sx s ->
       begin
         let convert t =
           if Timed.pure_test (leq_sort sx) _st &&
                Timed.pure_test (leq_sort _sp) s
           then Box(P,eq_true e.pos (to_term t))
           else t
         in
         let bx =
           try box_set_pos (snd (M.find x.elt vars)) e.pos
           with Not_found -> try
               let Expr(sx, d) = find_expr x.elt in
               let bx = Box(sx, Bindlib.box (make x.pos (HDef(sx,d)))) in
               box_set_pos bx e.pos
             with Not_found ->
               let d = find_value x.elt in
               Box(V, Bindlib.box (make x.pos (VDef(d))))
         in
         convert bx
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
        let Sort s = unsugar_sort s in
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
        let Sort sa = unsugar_sort a in
        let Sort sb = unsugar_sort b in
        let fn xk =
          let xk = (x.pos, Box(sa, vari x.pos xk)) in
          let vars = M.add x.elt xk vars in
          sort_filter sb (unsugar env vars f b)
        in
        Box(F(sa,sb), hfun e.pos sa sb x fn)
    | (EInfx(t,_)   , ST       ) -> unsugar env vars t _st
    | (EInfx(t,_)   , SP       ) ->
       let t = to_term (unsugar env vars t _st) in
       Box(P, eq_true e.pos t)
    (* Propositions. *)
    | (EFunc(t,a,b,l), SP      ) ->
        let a = unsugar env vars a s in
        let b = unsugar env vars b s in
        Box(P, func e.pos t l (to_prop a) (to_prop b))
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
        let Sort k = unsugar_sort k in
        let xs = ne_list_to_list xs in
        let rec build vars xs ex =
          match xs with
          | []    -> to_prop (unsugar env vars ex _sp)
          | x::xs -> let fn xk : pbox =
                       let xk = (x.pos, Box(k, vari x.pos xk)) in
                       let vars = M.add x.elt xk vars in
                       build vars xs ex
                     in
                     univ ex.pos x k fn
        in
        Box(P, build vars xs e)
    | (EExis(xs,k,e), SP       ) ->
        let Sort k = unsugar_sort k in
        let xs = ne_list_to_list xs in
        let rec build vars xs ex =
          match xs with
          | []    -> to_prop (unsugar env vars ex _sp)
          | x::xs -> let fn xk : pbox =
                       let xk = (x.pos, Box(k, vari x.pos xk)) in
                       let vars = M.add x.elt xk vars in
                       build vars xs ex
                     in
                     exis ex.pos x k fn
        in
        Box(P, build vars xs e)
    | (EFixM(k,o,x,e), s       ) ->
        end_by_prop k;
        let o = to_ordi (unsugar env vars o _so) in
        let Sort ks = unsugar_sort k in
        let fn xo =
          let xo = (x.pos, Box(ks, vari x.pos xo)) in
          let vars = M.add x.elt xo vars in
          sort_filter ks (unsugar env vars e k)
        in
        Box(ks, fixm e.pos ks o x fn (nil ()))
    | (EFixN(k,o,x,e) , s     ) ->
        end_by_prop k;
        let o = to_ordi (unsugar env vars o _so) in
        let Sort ks = unsugar_sort k in
        let fn xo =
          let xo = (x.pos, Box(ks, vari x.pos xo)) in
          let vars = M.add x.elt xo vars in
          sort_filter ks (unsugar env vars e k)
        in
        Box(ks, fixn e.pos ks o x fn (nil ()))
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
    | (ELAbs(args,t,l), SV _   ) ->
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
              Box(V, labs e.pos l ao x fn)
          | (x     , y::xs) ->
              assert (l = NoLz);
              let t = make e.pos (ELAbs((y,xs),t,l)) in
              let t = make e.pos (ELAbs((x,[]),t,l)) in
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
    | (ELAbs(_,_,_) , ST       )
    | (EScis        , ST       ) ->
        begin
          match unsugar env vars e _sv with
          | Box(V,v) -> Box(T, valu e.pos v)
          | _        -> assert false
        end
    (* Terms. *)
    | (EAppl(t,u,l) , ST       ) ->
        let t = to_term (unsugar env vars t _st) in
        let u = to_term (unsugar env vars u _st) in
        Box(T, appl e.pos l t u)
    | (EAppl(_)     , SP       ) ->
        let t = to_term (unsugar env vars e _st) in
        Box(P, eq_true e.pos t)
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
    | (EProj(_)     , ST       ) ->
         let rec fn ls e =
           match e.elt with
           | EProj(v,r,l) ->
              begin
                match !r with
                | `V -> let v = to_valu (unsugar env vars v _sv) in
                        Box(T, t_proj e.pos (proj e.pos v l) ls)
                | `T -> fn ((e.pos,l)::ls) v
              end
           | _ ->
              let t = to_term (unsugar env vars e _st) in
              Box(T, t_proj e.pos t ls)
         in
         fn [] e
    | (ECase(v,r,l) , ST       ) ->
        begin
          let fn ((c, argo), t) =
            let (x, ao) = Option.default (none "_", None) argo in
            let f xx =
              let xx = (x.pos, Box(V, vari x.pos xx)) in
              let vars = M.add x.elt xx vars in
              to_term (unsugar env vars t _st)
            in
            (c.elt, (c.pos, x, f))
          in
          let get_pos (p,_,_) = p in
          let gn m (k,v) =
            if A.mem k m then already_matched (make (get_pos v) k);
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
    | (EFixY(a,v)   , ST       ) ->
        let fn x =
          let x = (a.pos, Box(T, vari a.pos x)) in
          let vars = M.add a.elt x vars in
          to_valu (unsugar env vars v _sv)
        in
        Box(T, fixy e.pos a fn)
    | (EPrnt(s)     , ST       ) ->
        Box(T, prnt e.pos s)
    | (ERepl(t,u,p) , ST       ) ->
        let t = to_term (unsugar env vars t _st) in
        let u = to_term (unsugar env vars u _st) in
        let p =
          match p with
          | None   -> None
          | Some p -> Some (to_term (unsugar env vars p _st))
        in
        Box(T, repl e.pos t u p)
    | (EDelm(u)     , ST       ) ->
        let u = to_term (unsugar env vars u _st) in
        Box(T, delm e.pos u)
    (* Type annotations. *)
    | (ECoer(u,v,a) , SV _     ) when leq_sort u s ->
        let v = to_valu (unsugar env vars v s) in
        let a = to_prop (unsugar env vars a _sp) in
        Box(V, coer e.pos VoT_V v a)
    | (ECoer(u,t,a)   , ST     ) when leq_sort u s ->
        let t = to_term (unsugar env vars t _st) in
        let a = to_prop (unsugar env vars a _sp) in
        Box(T, coer e.pos VoT_T t a)
    | (ESuch(u,v,j,r), (SV _|ST)) when leq_sort u s ->
        let xs = map_ne_list (fun (x,s) -> (x, unsugar_sort s)) v in
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
                try
                  match snd (M.find x.elt vars) with
                  | Box(V,v) -> sv_valu v
                  | Box(S,s) -> sv_stac s
                  | Box(_,_) -> assert false (* should not happen *)
                with Not_found ->
                  try
                    let v = make None (VDef (find_value x.elt)) in
                    sv_valu (Bindlib.box v)
                  with Not_found ->
                    assert false (* should not happen *)
              end
        in
        begin
          match s.elt with
          | SV _ -> Box(V, such e.pos VoT_V d sv (build_seq VoT_V vars d))
          | ST   -> Box(T, such e.pos VoT_T d sv (build_seq VoT_T vars d))
          | _    -> assert false (* should not happen *)
        end
    (* Ordinals. *)
    | (EPSet(u,l,a) , SV _     ) when leq_sort u s
                                 -> let v = to_valu (unsugar env vars a s) in
                                    Box(V, pset e.pos l VoT_V v)
    | (EPSet(u,l,a) , ST       ) when leq_sort u s
                                 -> let t = to_term (unsugar env vars a s) in
                                    Box(T, pset e.pos l VoT_T t)
    | (EConv        , SO       ) -> Box(O, conv e.pos)
    | (ESucc(o,n)   , SO       ) ->
        assert (n >= 0);
        let o = to_ordi (unsugar env vars o _so) in
        let rec fn n =
          if n = 0 then o else succ e.pos (fn (n-1)) in
        Box(O, fn n)
    | (EGoal(str)   , SV _     ) -> Box(V, goal e.pos V str)
    | (EGoal(str)   , ST       ) -> Box(T, to_term (Box(V, goal e.pos V str)))
    | (EGoal(str)   , SS       ) -> Box(S, goal e.pos S str)
    | (_, SV store) when store <> None ->
       let v = Bindlib.new_var (mk_free V) "x" in
       let t = to_term (unsugar env vars e (make s.pos ST)) in
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
  | Include  of string
  | Def_list of toplevel list
  | Glbl_set of set_param
  | Infix    of string * infix

let evari _loc x = make _loc (EVari(x, new_sort_uvar None))

let sort_def : strloc -> raw_sort -> toplevel = fun id s ->
  Sort_def(id,s)

let expr_def : strloc -> (strloc * raw_sort) list -> raw_sort option
               -> raw_ex -> toplevel = fun id args s e ->
  let s = sort_from_opt s in
  let f (id,s) e = none (EHOFn(id,s,e)) in
  let e = List.fold_right f args e in
  let f (_ ,a) s = none (SFun(a,s)) in
  let s = List.fold_right f args s in
  Expr_def(id,s,e)

let filter_args : string -> (strloc * raw_sort) list -> raw_ex ->
                  (strloc * raw_sort) list =
  fun id args e ->
    let changed = Array.make (List.length args) false in
    let rec fn e stack bounded =
      match e.elt with
      | EVari(x,_) when x.elt = id ->
         let rec gn i stack args =
           match (stack, args) with
           | (({elt = EVari(y,_)}::s), ((z,_)::a))
                when y.elt = z.elt && not (List.mem y.elt bounded) ->
              gn (i+1) s a
           | ((_::s), (_::a)) -> changed.(i) <- true; gn (i+1) s a
           | ([], (_::a)) -> changed.(i) <- true; gn (i+1) [] a
           | (_, [])     -> ()
         in
         gn 0 stack args
      | EVari(_) -> ()
      | EHOAp(e,sx,es) ->
         List.iter (fun e -> fn e [] bounded) es;
         fn e (es @ stack) bounded
      | EInfx _ -> ()
      | EHOFn(x,k,f) -> if x.elt <> id then fn e stack (x.elt::bounded)
      | EFunc(_,a,b,_) -> fn a stack bounded; fn b stack bounded
      | EUnit -> ()
      | EDSum(l) -> List.iter (fun (_,a) ->
                        match a with None -> ()
                                   | Some a -> fn a stack bounded) l
      | EProd(l,_) ->  List.iter (fun (_,a) -> fn a stack bounded) l
      | EUniv((x,xs),k,e)
      | EExis((x,xs),k,e) ->
         let xs = List.map (fun x -> x.elt) (x::xs) in
         if not (List.mem id xs) then fn e stack (xs @ bounded)
      | EFixM(k,o,x,e)
      | EFixN(k,o,x,e) -> fn o stack bounded;
                          if x.elt <> id then fn e stack (x.elt::bounded)
      | EMemb(t,a) -> fn t stack bounded; fn a stack bounded
      | ERest(a,eq)
      | EImpl(eq,a) ->
         begin
           match eq with
           | EEquiv(t,_,u) -> fn t stack bounded; fn u stack bounded
           | ENoBox(v)     -> fn v stack bounded
         end;
         begin
           match a with
           | None   -> ()
           | Some a -> fn a stack bounded
         end
      | ELAbs((l1,l2),t,_) ->
         let l = List.map (fun (x,ao) ->
                     begin
                       match ao with
                       | None   -> ()
                       | Some a -> fn a stack bounded
                     end;
                     x.elt) (l1 :: l2)
         in
         if not (List.mem id l) then fn t stack (l @ bounded)
      | ECons(_,vo) ->
         begin
           match vo with
           | None       -> ()
           | Some (v,r) -> fn v stack bounded
         end
      | EReco(l) ->
         List.iter (fun (_,v,_) -> fn v stack bounded) l
      | EScis -> ()
      | EGoal _ -> ()
      | EAppl(t,u,_)
      | ESequ(t,u) -> fn t stack bounded; fn u stack bounded
      | EMAbs(arg,t) ->
         if arg.elt <> id then fn t stack (arg.elt::bounded)
      | EName(s,t) -> fn s stack bounded; fn t stack bounded
      | EProj(v,r,_) -> fn v stack bounded
      | ECase(v,r,l) ->
         begin
           fn v stack bounded;
           let fn ((_, argo), t) =
             let (x, ao) = Option.default (none "_", None) argo in
             if x.elt <> id then
               match ao with
               | None   -> ()
               | Some a -> fn a stack (x.elt::bounded)
           in
           List.iter fn l
         end
      | EFixY(a,v) ->
         if a.elt<>id then fn v stack (a.elt :: bounded)
      | EPrnt(_) -> ()
      | ERepl(t,u,p) -> fn t stack bounded; fn u stack bounded;
                        begin
                          match p with
                          | None -> ()
                          | Some p -> fn p stack bounded
                        end
      | EDelm(u) -> fn u stack bounded
      | ECoer(u,t,a) -> fn t stack bounded; fn a stack bounded
      | ESuch(u,(x,vs),j,v) ->
         let l = List.map (fun (x,_) -> x.elt) (x::vs) in
         if not (List.mem id l) then fn v stack (l @ bounded)
      | EPSet(u,_,a) -> fn a stack bounded
      | EConv -> ()
      | ESucc(o,_) -> fn o stack bounded
    in
    fn e [] [];
    let args = List.mapi (fun i a -> (i, a)) args in
    let args = List.filter (fun (i,a) -> changed.(i)) args in
    List.map snd args

let type_def : pos -> [`Non | `Rec | `CoRec] -> strloc
               -> (strloc * raw_sort option) list
               -> raw_ex -> toplevel = fun _loc r id args e ->
  let args = List.map (fun (x,k) -> (x, sort_from_opt k)) args in
  let rec binds : (strloc * raw_sort) list -> raw_ex -> raw_ex =
    fun args s ->
      match args with
      | []      -> s
      | (v,k)::args ->
         make (Some _loc) (EHOFn(v,k, binds args s))
  in
  let applies : (strloc * raw_sort) list -> raw_ex -> raw_ex =
    fun args s ->
      match args with
      | []      -> s
      | _::_ ->
         let args =
           List.map (fun (v,k) -> make v.pos (EVari(v,k))) args
         in
         make (Some _loc) (EHOAp(s,new_sort_uvar None, args))
  in
  let lift e =
    let ch_args = filter_args id.elt args e in
    let e = if List.length ch_args <> List.length args then
              let s1 = new_sort_uvar None in
              let s2 = new_sort_uvar None in
              let s3 = new_sort_uvar None in
              none (EHOAp(none (EHOFn(id,s1,e)),s2,
                              [binds args
                                     (applies ch_args
                                              (none (EVari(id,s3))))]))
            else e
    in
    (ch_args, e)
  in
  let e1 =
    match r with
    | `Non   -> e
    | `Rec   ->
      let (args, e) = lift e in
      let e =
        EFixM(new_sort_uvar None, none EConv, id, binds args e) in
      applies args (in_pos _loc e)
    | `CoRec ->
      let (args, e) = lift e in
      let e =
        EFixN(new_sort_uvar None, none EConv, id, binds args e)
      in applies args (in_pos _loc e)
  in
  let d1 = expr_def id args (Some (none SP)) e1 in
  if r = `Non then d1 else
    begin
      let id2 = make id.pos (id.elt ^ "#") in
      let s = evari None (none "s#") in
      let e2 =
        let (args, e) = lift e in
        match r with
        | `Non   -> assert false
        | `Rec   -> let e = EFixM(new_sort_uvar None, s, id, binds args e) in
                    applies args (in_pos _loc e)
        | `CoRec -> let e = EFixN(new_sort_uvar None, s, id, binds args e) in
                    applies args (in_pos _loc e)
      in
      let args = (none "s#", none SO) :: args in
      let d2 = expr_def id2 args (Some (none SP)) e2 in
      Def_list [d1;d2]
    end

let expr_def : strloc -> (strloc * raw_sort option) list -> raw_sort option
               -> raw_ex -> toplevel = fun id args s e ->
  let args = List.map (fun (x,k) -> (x, sort_from_opt k)) args in
  expr_def id args s e

type rec_t = [ `Non | `Rec ]

let val_def : rec_t -> strloc -> raw_ex -> raw_ex -> toplevel =
    fun r id a t ->
  let t = if r = `Non then t else make t.pos (EFixY(id, t)) in
  Valu_def(id, a, t)

let check_sub : raw_ex -> bool -> raw_ex -> toplevel = fun a r b ->
  Chck_sub(a,r,b)

(** syntactic sugars *)

let tuple_type _loc bs =
  let fn i a = (none (string_of_int (i+1)), a) in
  in_pos _loc (EProd(List.mapi fn bs, true))

let tuple_term _loc ts =
  let fn i t = (none (string_of_int (i+1)), t, ref `T) in
  in_pos _loc (EReco(List.mapi fn ts))

let record _loc fs =
  let fn (l, ao) =
    let a = Option.default (evari l.pos l) ao in
    (l, a, ref `T)
  in
  in_pos _loc (EReco(List.map fn fs))

let erest a l =
  List.fold_left (fun a x ->
      none (ERest(Some a,ENoBox(evari x.pos x)))) a l

let eimpl a l =
  List.fold_left (fun a x ->
      none (EImpl(ENoBox(evari None x), Some a))) a l

let euniv _loc x xs s a =
  let s = match s with Some s -> s | None -> new_sort_uvar (Some x) in
  let a = match s.elt with SV _ -> eimpl a (x::xs) | _ -> a in
  in_pos _loc (EUniv((x,xs), s, a))

let eexis _loc x xs s a =
  let s = match s with Some s -> s | None -> new_sort_uvar (Some x) in
  let a = match s.elt with SV _ -> erest a (x::xs) | _ -> a in
  in_pos _loc (EExis((x,xs), s, a))

let euniv_in _loc x xs a b =
  let p x = in_pos _loc x in
  let c = List.fold_right (fun x c ->
    (* FIXME #21: notation for partial dependant product ? *)
    p (EFunc(Effect.bot, p (EMemb(evari (Some _loc) x, a)), c, NoLz))) (x::xs) b
  in
  p (EUniv((x,xs),p sv,c))

let eexis_in _loc x xs a b =
  let p x = in_pos _loc x in
  let l = List.map (fun x -> p (EMemb(evari (Some _loc) x, a))) (x::xs) in
  let c = tuple_type _loc (l @ [b]) in
  (* Alternatives, only with pair
  let c = List.fold_right (fun x c ->
    tuple_type _loc [p (EMemb(p (EVari(x,[])), a)); c]) (x::xs) b
  in
  *)
  p (EExis((x,xs),p sv,c))

let esett _loc x a =
  let a = none (EMemb(evari x.pos x, a)) in
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
  make _loc (EDSum [(none "true", None) ; (none "false", None)])

(* "if c then t else e" := "case t:bool of { Tru[_] -> t | Fls[_] -> e }" *)
let if_then_else _loc c t e =
  let e = match e with Some e -> e | None -> none EUnit in
  let no_arg c t = ((none c, None), t) in
  let pats = [ no_arg "true" t ; no_arg "false" e ] in
  in_pos _loc (ECase(c, ref `T, pats))

(* "let x : a = t in u" := "(fun (x:a) -> u) (t:a)" *)
let let_binding _loc r arg t u =
  match arg with
  | `LetArgVar(id,ao) ->
     let t = if r = `Non then t else make t.pos (EFixY(id, t)) in
     let t =
        match ao with
        | None   -> t
        | Some a -> make t.pos (ECoer(new_sort_uvar None,t,a))
      in
      in_pos _loc (EAppl(make u.pos (ELAbs(((id, ao), []), u, NoLz)), t, NoLz))
  | `LetArgRec(fs)    ->
      if r <> `Non then Lex.give_up (); (* "let rec" meaningless here. *)
      let xs = List.map snd fs in
      let u = make u.pos (ELAbs((List.hd xs, List.tl xs), u, NoLz)) in
      let x = none "$rec$" in
      let fn u (l,_) =
        let pr = none (EProj(evari None x, ref `T,  l)) in
        make u.pos (EAppl(u, pr, NoLz))
      in
      let u = List.fold_left fn u fs in
      in_pos _loc (EAppl(make u.pos (ELAbs(((x, None), []), u, NoLz)), t, NoLz))
  | `LetArgTup(fs)    ->
      if r <> `Non then Lex.give_up (); (* "let rec" meaningless here. *)
      let u = make u.pos (ELAbs((List.hd fs, List.tl fs), u, NoLz)) in
      let x = none "$tup$" in
      let is = List.mapi (fun i _ -> none (string_of_int (i+1))) fs in
      let fn u l =
        let pr = none (EProj(evari None x, ref `T,  l)) in
        make u.pos (EAppl(u, pr, NoLz))
      in
      let u = List.fold_left fn u is in
      in_pos _loc (EAppl(make u.pos (ELAbs(((x, None), []), u, NoLz)), t, NoLz))

let pattern_matching _loc t ps =
  let fn ((c,pat), t) =
    let (pat, t) =
      match pat with
      | None                    -> (None        , t)
      | Some(`LetArgVar(id,ao)) -> (Some (id,ao), t)
      | Some(`LetArgRec(fs)   ) ->
          let xs = List.map snd fs in
          let t = make t.pos (ELAbs((List.hd xs, List.tl xs), t, NoLz)) in
          let x = none "$rec$" in
          let fn t (l,_) =
            let pr = none (EProj(evari None x, ref `T,  l)) in
            make t.pos (EAppl(t, pr, NoLz))
          in
          (Some (x, None), List.fold_left fn t fs)
      | Some(`LetArgTup(fs)   ) ->
          let t = make t.pos (ELAbs((List.hd fs, List.tl fs), t, NoLz)) in
          let x = none "$tup$" in
          let is = List.mapi (fun i _ -> none (string_of_int (i+1))) fs in
          let fn t l =
            let pr = none (EProj(evari None x, ref `T,  l)) in
            make t.pos (EAppl(t, pr, NoLz))
          in
          (Some (x, None), List.fold_left fn t is)
    in ((c,pat), t)
  in
  let ps = List.map fn ps in
  in_pos _loc (ECase(t, ref `T, ps))

(* (strloc * (strloc * raw_ex option) option) * raw_ex *)

(* Boolean values. *)
let v_bool _loc b =
  let b = ECons(none (if b then "true" else "false"), None) in
  in_pos _loc (ECoer(_sv, in_pos _loc b, p_bool None))

(* Empty list. *)
let v_nil _loc =
  in_pos _loc (ECons(in_pos _loc "Nil", None))

(* Cons on lists. *)
let v_cons _loc t u =
  let args = [ (none "hd", t, ref `T) ; (none "tl", u, ref `T) ] in
  let arg = (none (EReco(args)), ref `T) in
  in_pos _loc (ECons(none "Cons", Some arg))

let from_int _loc n =
  let zero = evari (Some _loc) (in_pos _loc "zero") in
  let succ = evari (Some _loc) (in_pos _loc "succ") in
  let dble = evari (Some _loc) (in_pos _loc "dble") in
  let opp  = evari (Some _loc) (in_pos _loc "opp" ) in
  let rec fn n =
    if n = 0 then zero
    else if n < 0 then in_pos _loc (EAppl(opp,fn (- n), NoLz))
    else
      let t = in_pos _loc (EAppl(dble,fn (n/2), NoLz)) in
      if n mod 2 = 0 then t
      else in_pos _loc (EAppl(succ,t,NoLz))
  in
  fn n

(* Sytactic sugar for proofs *)

(* "qed" := "{}" *)
let qed _loc =
  in_pos _loc (EReco([]))

(* "show a" := "(qed : a"
   "show a using p" := "p : a" *)
let show _loc a t =
  let (s,t) = match t with
    | None   -> (_sv, qed _loc)
    | Some t -> (new_sort_uvar None, t)
  in
  in_pos _loc (ECoer(s, t, a))

(* "show a == b using t_1
           == c"
   := "(t_1 : a == b); (qed : b == c)" *)
let equations _loc _loc_a a eqns =
  let rec fn t l = (* t is a proof of a = x *)
    match l with
    | [] -> (match t with None -> assert false | Some t -> t)
    | (_loc_y,y,prf)::l ->
       let a = none (ERest(None, EEquiv(a,true,y))) in
       let (s,prf) = match prf with
         | None   -> (_sv, qed _loc)
         | Some t -> (new_sort_uvar None, t)
       in
       let u = in_pos (merge _loc_a _loc_y) (ECoer(s, prf, a)) in
       let t = match t with
               | None   -> Some u
               | Some t -> Some (in_pos _loc (ESequ(t,u)))
       in
       fn t l
  in
  fn None eqns

(* "use a" := "a" *)
let use _loc t =
  t

(* "from a; p" := "let _ = p : a in {}" *)
let showing _loc a q p =
  let q = match q with
    | None   -> qed _loc
    | Some q -> q
  in
  let_binding _loc `Non (`LetArgVar(none "",Some a)) p q

(* "suppose p t" := "fun _:p { t }" *)
let suppose _loc props t =
  let args = List.map (fun p -> (none "_", Some p)) props in
  in_pos _loc (ELAbs((List.hd args, List.tl args),t,NoLz))

(* "assume t" := "let x = t;
                  (case x { true -> qed false -> qed } ; x == true" *)
let assume _loc t q p =
  let q = match q with
    | None   -> qed _loc
    | Some q -> q
  in
  in_pos _loc (ECase(t, ref `T,
    [ ((none "false", None), q)
    ; ((none "true" , None), p)]))
