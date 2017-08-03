let closed : type a. ?olist:o ex loc list -> a ex loc -> bool
  = fun ?(olist=[]) e ->
  let rec closed : type a. a ex loc -> bool = fun e ->
    match sort e with (O, e) when Compare.is_in e olist -> false | _ ->
    match e.elt with
    | Vari(_)     -> false
    | HFun(_,_,f) -> bndr_closed f
    | HApp(_,f,a) -> closed f && closed a
    | HDef(_,_)   -> true (* assumed closed *)
    | Func(a,b)   -> closed a && closed b
    | Prod(m)     -> A.for_all (fun _ (_,a) -> closed a) m
    | DSum(m)     -> A.for_all (fun _ (_,a) -> closed a) m
    | Univ(_,f)   -> bndr_closed f
    | Exis(_,f)   -> bndr_closed f
    | FixM(o,f)   -> bndr_closed f && closed o
    | FixN(o,f)   -> bndr_closed f && closed o
    | Memb(t,a)   -> closed t && closed a
    | Rest(a,c)   -> closed a && cond_closed c
    | Impl(c,a)   -> cond_closed c && closed a
    | LAbs(a,f)   -> bndr_closed f && Option.default_map true closed a
    | Cons(_,v)   -> closed v
    | Reco(m)     -> A.for_all (fun _ (_,a) -> closed a) m
    | Scis        -> true
    | VDef(_)     -> true (* assumed closed *)
    | Valu(v)     -> closed v
    | Appl(t,u)   -> closed t && closed u
    | MAbs(f)     -> bndr_closed f
    | Name(s,t)   -> closed s && closed t
    | Proj(v,_)   -> closed v
    | Case(v,m)   -> closed v && A.for_all (fun _ (_,f) -> bndr_closed f) m
    | FixY(f,v)   -> bndr_closed f && closed v
    | Prnt(_)     -> true
    | Epsi        -> true
    | Push(v,s)   -> closed v && closed s
    | Fram(t,s)   -> closed t && closed s
    | Zero        -> true
    | Conv        -> true
    | Succ(o)     -> closed o
    | OWMu(o,t,f) -> bndr_closed f && closed o && closed t
    | OWNu(o,t,f) -> bndr_closed f && closed o && closed t
    | OSch(o,_,s) -> sch_closed s && Option.default_map true closed o
    | VTyp(v,a)   -> closed v && closed a
    | TTyp(t,a)   -> closed t && closed a
    | VLam(_,f)   -> bndr_closed f
    | TLam(_,f)   -> bndr_closed f
    | ITag(_,_)   -> true
    | Dumm        -> true
    | VWit(f,a,b) -> bndr_closed f && closed a && closed b
    | SWit(f,a)   -> bndr_closed f && closed a
    | UWit(_,t,f) -> bndr_closed f && closed t
    | EWit(_,t,f) -> bndr_closed f && closed t
    | UVar(_,_)   -> true
    | Goal(_,_)   -> true
  and cond_closed c =
    match c with
    | Equiv(t,_,u) -> closed t && closed u
    | Posit(o)     -> closed o
    | NoBox(v)     -> closed v
  and sch_closed sch =
    match sch with
    | FixSch({fsch_judge = (f,mf)}) -> bndr_closed f && mbinder_closed mf
    | SubSch({ssch_judge = mf    }) -> mbinder_closed mf
  in closed e
