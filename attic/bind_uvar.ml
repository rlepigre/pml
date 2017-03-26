let bind_uvar : type a. a sort -> a uvar -> prop -> (a, p) bndr =
  let rec fn : type a b. a sort -> b sort -> a uvar -> b ex loc
               -> a ex bindbox -> b box =
    fun sa sb uv e x ->
      let e = Norm.whnf e in
      Printf.eprintf "coucou %a\n%!" Print.print_ex e;
      match e.elt with
      | Vari(x)     -> vari None x
      | HFun(s,t,b) -> hfun e.pos s t (bndr_name b)
                         (fun y -> fn sa t uv (bndr_subst b (mk_free y)) x)
      | HApp(s,a,b) -> happ e.pos s (fn sa (F(s,sb)) uv a x) (fn sa s uv b x)
      | HDef(_,_)   -> box e (* NOTE no unification variables in defs. *)
      | Func(a,b)   -> func e.pos (fn sa P uv a x) (fn sa P uv b x)
      | Prod(m)     -> let gn (l,a) = (l, fn sa P uv a x) in
                       prod e.pos (M.map gn m)
      | DSum(m)     -> let gn (c,a) = (c, fn sa P uv a x) in
                       dsum e.pos (M.map gn m)
      | Univ(s,b)   -> univ e.pos (bndr_name b) s
                         (fun y -> fn sa sb uv (bndr_subst b (mk_free y)) x)
      | Exis(s,b)   -> exis e.pos (bndr_name b) s
                         (fun y -> fn sa sb uv (bndr_subst b (mk_free y)) x)
      | FixM(o,b)   -> fixm e.pos (fn sa O uv o x) (bndr_name b)
                         (fun y -> fn sa P uv (bndr_subst b (mk_free y)) x)
      | FixN(o,b)   -> fixm e.pos (fn sa O uv o x) (bndr_name b)
                         (fun y -> fn sa P uv (bndr_subst b (mk_free y)) x)
      | Memb(t,a)   -> memb e.pos (fn sa T uv t x) (fn sa P uv a x)
      | Rest(a,c)   -> let c =
                         match c with
                         | Equiv(t,b,u) ->
                             equiv (fn sa T uv t x) b (fn sa T uv u x)
                         | Posit(o)     ->
                             posit (fn sa O uv o x)
                         | NoBox(v)     ->
                             nobox (fn sa V uv v x)
                       in rest e.pos (fn sa P uv a x) c
      | Impl(c,a)   -> let c =
                         match c with
                         | Equiv(t,b,u) ->
                             equiv (fn sa T uv t x) b (fn sa T uv u x)
                         | Posit(o)     ->
                             posit (fn sa O uv o x)
                         | NoBox(v)     ->
                             nobox (fn sa V uv v x)
                       in impl e.pos c (fn sa P uv a x)
      | LAbs(ao,b)  -> labs e.pos (Option.map (fun a -> fn sa P uv a x) ao)
                         (bndr_name b)
                         (fun y -> fn sa T uv (bndr_subst b (mk_free y)) x)
      | Cons(c,v)   -> cons e.pos c (fn sa V uv v x)
      | Reco(m)     -> let gn (l,v) = (l, fn sa V uv v x) in
                       reco e.pos (M.map gn m)
      | Scis        -> scis e.pos
      | VDef(_)     -> box e (* NOTE no unification variables in defs. *)
      | Valu(v)     -> valu e.pos (fn sa V uv v x)
      | Appl(t,u)   -> appl e.pos (fn sa T uv t x) (fn sa T uv u x)
      | MAbs(b)     -> mabs e.pos (bndr_name b)
                         (fun y -> fn sa T uv (bndr_subst b (mk_free y)) x)
      | Name(s,t)   -> name e.pos (fn sa S uv s x) (fn sa T uv t x)
      | Proj(v,l)   -> proj e.pos (fn sa V uv v x) l
      | Case(v,m)   -> let gn (p,b) =
                         let f y = fn sa T uv (bndr_subst b (mk_free y)) x in
                         (p, bndr_name b, f)
                       in
                       case e.pos (fn sa V uv v x) (M.map gn m)
      | FixY(t,v)   -> fixy e.pos (fn sa T uv t x) (fn sa V uv v x)
      | Epsi        -> box e
      | Push(v,s)   -> push e.pos (fn sa V uv v x) (fn sa S uv s x)
      | Fram(t,s)   -> fram e.pos (fn sa T uv t x) (fn sa S uv s x)
      | Conv        -> box e
      | Succ(o)     -> succ e.pos (fn sa O uv o x)
      | VTyp(v,a)   -> vtyp e.pos (fn sa V uv v x) (fn sa P uv a x)
      | TTyp(t,a)   -> ttyp e.pos (fn sa T uv t x) (fn sa P uv a x)
      | VLam(s,b)   -> vlam e.pos (bndr_name b) s
                         (fun y -> fn sa V uv (bndr_subst b (mk_free y)) x)
      | TLam(s,b)   -> tlam e.pos (bndr_name b) s
                         (fun y -> fn sa T uv (bndr_subst b (mk_free y)) x)
      | ITag(_)     -> box e
      | Dumm        -> box e
      | VWit(b,a,c) -> vdwit e.pos (bndr_name b)
                         (fun y -> fn sa T uv (bndr_subst b (mk_free y)) x)
                         (fun y -> fn sa P uv (bndr_subst a (mk_free y)) x)
                         (fn sa P uv c x)
      | SWit(b,a)   -> swit e.pos (bndr_name b)
                         (fun y -> fn sa T uv (bndr_subst b (mk_free y)) x)
                         (fn sa P uv a x)
      | UWit(s,t,b) -> uwit e.pos (fn sa T uv t x) (bndr_name b) s
                         (fun y -> fn sa P uv (bndr_subst b (mk_free y)) x)
      | EWit(s,t,b) -> ewit e.pos (fn sa T uv t x) (bndr_name b) s
                            (fun y -> fn sa P uv (bndr_subst b (mk_free y)) x)
      | OWit(o,i,s) -> owit e.pos (fn sa O uv o x) i (gn sa uv s x)
      | UVar(t,v)   ->
          begin
            match eq_sort sa t with
            | Eq  -> if uvar_eq uv v then box_apply Pos.none x else box e
            | NEq -> box e
          end
  and gn : type a. a sort -> a uvar -> schema -> a ex bindbox
                                            -> schema Bindlib.bindbox =
    fun s uv sch x -> assert false (* FIXME *)
  in
  fun s uv e -> (None, unbox (bind mk_free "X0" (fn s P uv e)))
