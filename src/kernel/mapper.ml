open Extra
open Ast
open Pos
open Sorts

(* a mapper may raise the exception Default *)
type recall = { recall : 'a. 'a ex loc -> 'a ebox
              ; recals : 'a 'b. ('a, 'b) fix_args -> ('a, 'b) fbox
              ; default : 'a. 'a ex loc -> 'a ebox}
type mapper = { mapper : 'a. recall -> 'a ex loc -> 'a ebox }

let defmapper =
  let mapper {default} x =
    let res = default x in
    if Bindlib.is_closed res then Bindlib.box x else res
  in
  {mapper}

let map : type a. ?mapper:mapper -> a ex loc -> a ebox
  = fun ?(mapper=defmapper) e ->
    let rec map_cond c =
      match c with
      | Equiv(t,b,u) -> equiv (map t) b (map u)
      | NoBox(v)     -> nobox (map v)

    and map_args : type a b.(a, b) fix_args -> (a, b) fbox = fun l ->
      match l with
      | Nil      -> nil()
      | Cns(e,l) -> cns (map e) (map_args l)

    and map : type a. a ex loc -> a ebox = fun e ->
      let e = Norm.whnf e in

      let default : type a. a ex loc -> a ebox = fun e ->
        match e.elt with
        | HDef(_,_)     -> Bindlib.box e (* Assumed closed *)
        | HApp(s,f,a)   -> happ e.pos s (map f) (map a)
        | HFun(a,b,f)   -> hfun e.pos a b (bndr_name f)
                                (fun x -> map (bndr_subst f (mk_free a x)))
        | UWit(_)       -> Bindlib.box e
        | EWit(_)       -> Bindlib.box e
        | UVar(_,_)     -> Bindlib.box e
        | ITag(_,_)     -> Bindlib.box e
        | Goal(_,_)     -> Bindlib.box e

        | Func(t,a,b)   -> func e.pos t (map a) (map b)
        | Prod(m)       -> prod e.pos (A.map (fun (p,a) -> (p, map a)) m)
        | DSum(m)       -> dsum e.pos (A.map (fun (p,a) -> (p, map a)) m)
        | Univ(s,f)     -> univ e.pos (bndr_name f) s
                                (fun x -> map (bndr_subst f (mk_free s x)))
        | Exis(s,f)     -> exis e.pos (bndr_name f) s
                                (fun x -> map (bndr_subst f (mk_free s x)))
        | FixM(s,o,f,l) -> fixm e.pos s (map o) (bndr_name f)
                                (fun x -> map (bndr_subst f (mk_free s x)))
                                (map_args l)
        | FixN(s,o,f,l) -> fixn e.pos s (map o) (bndr_name f)
                                (fun x -> map (bndr_subst f (mk_free s x)))
                                (map_args l)
        | Memb(t,a)     -> memb e.pos (map t) (map a)
        | Rest(a,c)     -> rest e.pos (map a) (map_cond c)
        | Impl(c,a)     -> impl e.pos (map_cond c) (map a)

        | VWit(_)       -> Bindlib.box e
        | LAbs(a,f,t)   -> labs e.pos (Option.map map a) (bndr_name f)
                                (fun x -> map (bndr_subst f (mk_free V x)))
        | Cons(c,v)     -> cons e.pos c (map v)
        | Reco(m)       -> reco e.pos (A.map (fun (p,v) -> (p, map v)) m)
        | Scis          -> Bindlib.box e
        | VDef(_)       -> Bindlib.box e

        | Coer(t,e,a)   -> coer e.pos t (map e) (map a)
        | Such(t,d,r)   -> let sv =
                             match r.opt_var with
                             | SV_None    -> sv_none
                             | SV_Valu(v) -> sv_valu (map v)
                             | SV_Stac(s) -> sv_stac (map s)
                           in
                           let rec aux : type a b. (a, prop * b ex loc) bseq
                                 -> (a, prop * b ex loc) fseq =
                             fun b ->
                               match b with
                               | BLast(s,b) ->
                                  let x = Bindlib.binder_name b in
                                  let f x =
                                    let (p,e) =
                                      Bindlib.subst b (mk_free s x)
                                    in
                                    Bindlib.box_pair (map p) (map e)
                                  in
                                  FLast(s, Pos.none x, f)
                               | BMore(s,b) ->
                                  let x = Bindlib.binder_name b in
                                  let f x =
                                    aux (Bindlib.subst b (mk_free s x))
                                  in
                                  FMore(s, Pos.none x, f)
                                              in
                                              such e.pos t d sv (aux r.binder)
        | PSet(l,s,t)   -> pset e.pos l s (map t)

        | Valu(v)       -> valu e.pos (map v)
        | Appl(t,u)     -> appl e.pos (map t) (map u)
        | MAbs(f)       -> mabs e.pos (bndr_name f)
                                (fun x -> map (bndr_subst f (mk_free S x)))
        | Name(s,t)     -> name e.pos (map s) (map t)
        | Proj(v,l)     -> proj e.pos (map v) l
        | Case(v,m)     -> let fn (p,f) =
                             let fn x = map (bndr_subst f (mk_free V x)) in
                             (p, bndr_name f, fn)
                           in
                           case e.pos (map v) (A.map fn m)
        | FixY(f)       -> fixy e.pos (bndr_name f)
                                (fun x -> map (bndr_subst f (mk_free T x)))
        | Prnt(s)       -> prnt e.pos s
        | Repl(t,u)     -> repl e.pos (map t) (map u) None
        | Delm(u)       -> delm e.pos (map u)

        | SWit(_)       -> Bindlib.box e

        | Conv          -> Bindlib.box e
        | Succ(o)       -> succ e.pos (map o)
        | OWMu(_)       -> Bindlib.box e
        | OWNu(_)       -> Bindlib.box e
        | OSch(_)       -> Bindlib.box e
        | ESch(_)       -> Bindlib.box e
        | Vari(_,x)     -> vari e.pos x

        | VPtr _        -> Bindlib.box e
        | TPtr _        -> Bindlib.box e
        in
        mapper.mapper { recall = map; recals = map_args; default } e
      in map e

let lift : type a. a ex loc -> a ebox = fun e -> map e
