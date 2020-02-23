open Ast
open Hash
open Compare
open Uvars
open Sorts
open Pos
open Bindlib

(** This files deals with hash-consing of epsilons.

    This is crucial as epsilons leads to terms with a lot of shared terms,
    which if completely traverser would lead to an exponential complexity.

    Moreover, this is rendered more complex because epsilon may contain
    uninstanciated unification variables. Therefore, we use a hook in
    unfication variable to trigger rehashing of epsilon using that variable
    when it is instanciated.
 *)


(** Building modules for the different kind of epsilons *)

(** Value epsilon *)
module VWit = struct
  type t = vwit
  let hash = hash_vwit
  let equal (f1,a1,b1) (f2,a2,b2) =
    eq_bndr V f1 f2 && eq_expr a1 a2 && eq_expr b1 b2
  let vars (f, a, b) = bndr_uvars V f @ uvars a @ uvars b
end

module VWitHash = Hashtbl.Make(VWit)
let vwit_hash   = VWitHash.create 256

(** Quantifiers epsilon, both for UWit and EWit *)
module QWit = struct
  type t = Q:'a qwit -> t
  let hash (Q w) = hash_qwit w
  let equal (Q (s1,t1,b1)) (Q(s2,t2,b2)) =
    match eq_sort s1 s2 with
    | Eq.Eq -> eq_expr t1 t2 && eq_bndr s1 b1 b2
    | _ -> false
  let vars (Q(s, t, b)) = bndr_uvars s b @ uvars t
end

module QWitHash = Hashtbl.Make(QWit)
type aqwit = Q : ('a qwit, string) eps -> aqwit
let qwit_hash   = QWitHash.create 256

(** Ordinal epsilons *)
module OWit = struct
  type t = owit
  let hash = hash_owit
  let equal (o1,a1,b1) (o2,a2,b2) =
    eq_expr o1 o2 && eq_expr a1 a2 && eq_bndr O b1 b2
  let vars (o, a, b) = uvars o @ uvars a @ bndr_uvars O b
end

module OWitHash = Hashtbl.Make(OWit)
let owit_hash   = OWitHash.create 256

(** Stack epsilon *)
module SWit = struct
  type t = swit
  let hash = hash_swit
  let equal (b1,a1) (b2,a2) = eq_bndr S b1 b2 && eq_expr a1 a2
  let vars (b, a) = uvars a @ bndr_uvars S b
end

module SWitHash = Hashtbl.Make(SWit)
let swit_hash   = SWitHash.create 256

(** Induction schemas epsilons *)

module CWit = struct
  type t = schema
  let hash = hash_cwit
  let equal s1 s2 =
    match (s1, s2) with
    | (FixSch s1, FixSch s2) -> s1.fsch_index = s2.fsch_index
    | (SubSch s1, SubSch s2) -> s1.ssch_index = s2.ssch_index
    | (_        , _        ) -> false
  let vars s =
    match s with
    | FixSch s ->
       let (b, mb) = s.fsch_judge in
       let (_, mb) = unmbind mb in
       bndr_uvars T b @ uvars mb
    | SubSch s ->
       let mb = s.ssch_judge in
       let (_, f) = unmbind mb in
       let rec fn = function
         | Cst(e1,e2) -> uvars e1 @ uvars e2
         | Bnd(_ ,f ) -> let (_,f) = unbind f in fn f
       in
       fn f
end

module CWitHash = Hashtbl.Make(CWit)
let cwit_hash   = CWitHash.create 256

(** Reset all hash tables between proofs *)
let reset_epsilons () =
  VWitHash.clear vwit_hash;
  QWitHash.clear qwit_hash;
  OWitHash.clear owit_hash;
  SWitHash.clear swit_hash;
  CWitHash.clear cwit_hash

(** Test if a variable in a list of unification variables has been set *)
let exists_set l =
  List.exists (fun (U(_,v)) ->
      match !(v.uvar_val) with Set _ -> true | _ -> false) l

(** Functions building all the epsilons, only the first one is commented,
    the others are similar *)

let vwit : ctxt -> (v,t) bndr -> prop -> prop -> (vwit, string) eps * ctxt =
  fun ctx f a b ->
    let valu = (f,a,b) in
    try (VWitHash.find vwit_hash valu, ctx)
    with Not_found ->
      (** the function called when a unification variable is instanciated *)
      let rec refr ?(force=false) w =
        if force || exists_set !(w.vars) then
          begin
            let oldvars = !(w.vars) in
            (* recompute hashes and list of vars *)
            UTimed.(w.vars := VWit.vars valu);
            UTimed.(w.hash := VWit.hash valu);
            (* add hooks to eventual new unification variables,
               if a unif variables was instanciated with a term
               containing other variables *)
            List.iter (fun (U(_,v)) ->
                let same (U(_,w)) = v.uvar_key = w.uvar_key in
                if not (List.exists same oldvars)
                then uvar_hook v (fun () -> refr w)) !(w.vars);
            try
              (** May be this new witness ... was not new *)
              let w' = VWitHash.find vwit_hash valu in
              (*Printf.eprintf "merge vwit\n%!";*)
              UTimed.(w.valu := !(w'.valu));
              UTimed.(w.pure := !(w'.pure))
            with Not_found ->
              (** We re-add the witness to the hashtbl.
                  Remark: we do not remove the old one because to do so, we
                  would need to use Timed hashtbl, to support eventuel undo
                  of unifications *)
              VWitHash.add vwit_hash valu w
          end
      in
      let pure = (* must be lazy, see ast.ml definition of eps type *)
        Lazy.from_fun (fun () ->
            Pure.(pure a && pure b && pure (bndr_term f)))
      in
      (** we create a name for printing *)
      let v, ctx = new_var_in ctx (mk_free V) (bndr_name f).elt in
      (** and the final record *)
      let rec w = { vars = ref []
                  ; name = name_of v
                  ; hash = ref 0
                  ; refr = (fun () -> refr w)
                  ; valu = ref valu
                  ; pure = ref pure }
      in
      (** call refresh to force the first adding in the Hashtbl *)
      refr ~force:true w;
      (w, ctx)

(** wrapper for the above function applying the ast constructor *)
let vwit : ctxt -> (v,t) bndr -> prop -> prop -> valu * ctxt =
  fun ctx f a b ->
    let (eps, ctx) = vwit ctx f a b in
    (Pos.none (VWit eps), ctx)

(** The other function works in the same ... It would be nice
    to share mode code, but it is not easy because of GADT ...*)
let qwit : type a. ctxt -> a sort -> term -> (a,p) bndr
                -> (a qwit, string) eps * ctxt =
  fun ctx s t b ->
    let valu = (s,t,b) in
    let key = QWit.Q(valu) in
    try
      let Q(w) = QWitHash.find qwit_hash key in
      let (s',_,_) = !(w.valu) in
      match eq_sort s s' with
      | Eq.Eq -> (w, ctx)
      | _ -> assert false
    with Not_found ->
      let rec refr : ?force:bool -> (a qwit, string) eps -> unit
      = fun ?(force=false) w ->
        if force || exists_set !(w.vars) then
          begin
            let oldvars = !(w.vars) in
            UTimed.(w.vars := QWit.vars key);
            UTimed.(w.hash := QWit.hash key);
            List.iter (fun (U(_,v)) ->
                let same (U(_,w)) = v.uvar_key = w.uvar_key in
                if not (List.exists same oldvars)
                then uvar_hook v (fun () -> refr w)) !(w.vars);
            try
              let Q(w') = QWitHash.find qwit_hash key in
              (*Printf.eprintf "merge qwit\n%!";*)
              let (s',_,_) = !(w'.valu) in
              match eq_sort s s' with
              | Eq.Eq -> UTimed.(w.valu := !(w'.valu));
                         UTimed.(w.pure := !(w'.pure))
              | _ -> assert false
            with Not_found ->
              QWitHash.add qwit_hash key (Q w)
          end
      in
      let v, ctx = new_var_in ctx (mk_free V) (bndr_name b).elt in
      let pure =
        Lazy.from_fun (fun () ->
            Pure.(pure t && pure (bndr_term b)))
      in
      let rec w = { vars = ref []
                  ; name = name_of v
                  ; hash = ref 0
                  ; refr = (fun () -> refr w)
                  ; valu = ref valu
                  ; pure = ref pure }
      in
      refr ~force:true w;
      (w, ctx)

let uwit : type a. ctxt -> a sort -> term -> (a,p) bndr -> a ex loc * ctxt =
  fun ctx s t f ->
    let (eps, ctx) = qwit ctx s t f in
    (Pos.none (UWit eps), ctx)

let ewit : type a. ctxt -> a sort -> term -> (a,p) bndr -> a ex loc * ctxt =
  fun ctx s t f ->
    let (eps, ctx) = qwit ctx s t f in
    (Pos.none (EWit eps), ctx)

let owit : ctxt -> ordi -> term -> (o,p) bndr -> (owit, string) eps * ctxt =
  fun ctx o a b ->
    let valu = (o,a,b) in
    try (OWitHash.find owit_hash valu, ctx)
    with Not_found ->
      let rec refr ?(force=false) w =
        if force || exists_set !(w.vars) then
          begin
            let oldvars = !(w.vars) in
            UTimed.(w.vars := OWit.vars valu);
            UTimed.(w.hash := OWit.hash valu);
            List.iter (fun (U(_,v)) ->
                let same (U(_,w)) = v.uvar_key = w.uvar_key in
                if not (List.exists same oldvars)
                then uvar_hook v (fun () -> refr w)) !(w.vars);
            try
              let w' = OWitHash.find owit_hash valu in
              (*Printf.eprintf "merge owit\n%!";*)
              UTimed.(w.valu := !(w'.valu));
              UTimed.(w.pure := !(w'.pure))
            with Not_found ->
              OWitHash.add owit_hash valu w
          end
      in
      let v, ctx = new_var_in ctx (mk_free V) (bndr_name b).elt in
      let pure =
        Lazy.from_fun (fun () ->
            Pure.(pure o && pure a && pure (bndr_term b)))
      in
      let rec w = { vars = ref []
                  ; name = name_of v
                  ; hash = ref 0
                  ; refr = (fun () -> refr w)
                  ; valu = ref valu
                  ; pure = ref pure }
      in
      refr ~force:true w;
      (w, ctx)

let owmu : ctxt -> ordi -> term -> (o, p) bndr -> ordi * ctxt =
  fun ctx o t b ->
    let (eps, ctx) = owit ctx o t b in
    (Pos.none (OWMu eps), ctx)

let ownu : ctxt -> ordi -> term -> (o, p) bndr -> ordi * ctxt =
  fun ctx o t b ->
    let (eps, ctx) = owit ctx o t b in
    (Pos.none (OWNu eps), ctx)

let swit : ctxt -> (s,t) bndr -> prop -> (swit, string) eps * ctxt =
  fun ctx b s ->
    let valu = (b,s) in
    try (SWitHash.find swit_hash valu, ctx)
    with Not_found ->
      let rec refr ?(force=false) w =
        if force || exists_set !(w.vars) then
          begin
            let oldvars = !(w.vars) in
            UTimed.(w.vars := SWit.vars valu);
            UTimed.(w.hash := SWit.hash valu);
            List.iter (fun (U(_,v)) ->
                let same (U(_,w)) = v.uvar_key = w.uvar_key in
                if not (List.exists same oldvars)
                then uvar_hook v (fun () -> refr w)) !(w.vars);
            try
              let w' = SWitHash.find swit_hash valu in
              (*Printf.eprintf "merge owit\n%!";*)
              UTimed.(w.valu := !(w'.valu));
              UTimed.(w.pure := !(w'.pure))
            with Not_found ->
              SWitHash.add swit_hash valu w
          end
      in
      let v, ctx = new_var_in ctx (mk_free V) (bndr_name b).elt in
      let pure =
        Lazy.from_fun (fun () -> Pure.(pure (bndr_term b) && pure s))
      in
      let rec w = { vars = ref []
                  ; name = name_of v
                  ; hash = ref 0
                  ; refr = (fun () -> refr w)
                  ; valu = ref valu
                  ; pure = ref pure }
      in
      refr ~force:true w;
      (w, ctx)

let swit : ctxt -> (s,t) bndr -> prop -> stac * ctxt =
  fun ctx f a ->
    let (eps, ctx) = swit ctx f a in
    (Pos.none (SWit eps), ctx)

let esch_names names w =
  match w with
  | FixSch s ->
     let os, names = new_mvar_in names (mk_free O) (mbinder_names (snd s.fsch_judge)) in
     (names, ((Array.map name_of os), [||]))
  | SubSch s ->
     let os, p, names = unmbind_in names s.ssch_judge in
     let ss1 = Array.map name_of os in
     let rec fn names l p = match p with
       | Cst _    -> (names, Array.of_list (List.rev l))
       | Bnd(s,f) -> let (v,b,names) = unbind_in names f in
                     fn names (name_of v :: l) b
     in
     let names, ss2 = fn names [] p in
     (names, (ss1, ss2))

let cwit : ctxt -> schema -> seps * ctxt =
  fun ctx valu ->
    try (CWitHash.find cwit_hash valu, ctx)
    with Not_found ->
      let rec refr ?(force=false) w =
        if force || exists_set !(w.vars) then
          begin
            let oldvars = !(w.vars) in
            UTimed.(w.vars := CWit.vars valu);
            UTimed.(w.hash := CWit.hash valu);
            List.iter (fun (U(_,v)) ->
                let same (U(_,w)) = v.uvar_key = w.uvar_key in
                if not (List.exists same oldvars)
                then uvar_hook v (fun () -> refr w)) !(w.vars);
            try
              let w' = CWitHash.find cwit_hash valu in
              (*Printf.eprintf "merge owit\n%!";*)
              UTimed.(w.valu := !(w'.valu));
              UTimed.(w.pure := !(w'.pure))
            with Not_found ->
              CWitHash.add cwit_hash valu w
          end
      in
      let (ctx, t2) = esch_names ctx valu in
      let pure = Lazy.from_fun (fun () -> Pure.(pure_schema valu)) in
      let rec w = { vars = ref []
                  ; name = t2
                  ; hash = ref 0
                  ; refr = (fun () -> refr w)
                  ; valu = ref valu
                  ; pure = ref pure }
      in
      refr ~force:true w;
      (w, ctx)

let osch : int -> ordi option -> seps -> ordi =
  fun i o eps -> Pos.none (OSch(i, o, eps))

let esch : type a. a sort -> int -> seps -> a ex loc =
  fun s i eps -> Pos.none (ESch(s, i, eps))
