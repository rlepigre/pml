(** This module implements a constraint solver for finite sets *)

open Timed

module type Elt = sig
  type t

  val all : t list
  val print : out_channel -> t -> unit
end

module type FinSet = sig
  type elt
  type set = elt list
  (** type of a set of elt or a variable representing such a set *)
  type t

  (** construct a fixed set *)
  val known : elt list -> t
  (** full and empty set *)
  val bot   : t
  val top   : t

  (** creates a new variable representing a set *)
  val create : ?absent:set -> ?present:set -> unit -> t

  (** returns Some l is the set is fully known *)
  val complete : t -> elt list option

  (** returns true is the elt is in the set of the constraint to add it if
  consistent with the current constraints. No constraints are added if the
  function returns false *)
  val present : elt -> t -> bool

  (** returns true is the elt is not in the set of the constraint to remove
  it if consistent with the current constraints. No constraints are added if
  the function returns false *)
  val absent : elt -> t -> bool

  (** [sub s1 s2] test or force the constraints s1 subset of s2.
      [sub ~except:s0 s1 s2] test for s1 < (s2 union s0) which is
      the same as (s1 inter s0) < s2 *)
  val sub : ?except:set -> t -> t -> bool

  (** test for equality of add the constraint *)
  val eq : t -> t -> bool

  (** test subset of a fixed set in the current knowledge, but do not add any
  constraint *)
  val know_sub : t -> set -> bool

  (** test equality in the current knowledge. *)
  (* TODO: incomplete in the current version, may return false while the
      equality is known *)
  val know_eq : t -> t -> bool

  val hash : t -> int
end

module Make(T:Timed)(E:Elt) = struct

  type elt = E.t
  type set = E.t list

  let espr ch l = List.iter (Printf.fprintf ch "%a;" E.print) l

  type constraints = { uiden : int
                     ; absen : set ref
                     ; prese : set ref
                     ; lower : (constraints * set) list ref
                     ; upper : (constraints * set) list ref
                     }

  type deco =
    | Known of set
    | Unkno of constraints

  type t = deco


  let known l = Known l
  let top = known E.all
  let bot = known []

  let complete : deco -> set option = fun v ->
    match v with
    | Known l   -> Some l
    | Unkno cts ->
       let (known, res) =
         List.fold_left (fun (known, acc) eff ->
             let b1 = List.mem eff !(cts.absen) in
             let b2 = List.mem eff !(cts.prese) in
             assert (not b1 || not b2);
             (known && (b1 || b2), if b2 then eff :: acc else acc)
           ) (true, []) E.all
       in
       if known then Some res else None

  let cpr ch c = Printf.fprintf ch "[%d %a^%a]" c.uiden
                                espr !(c.prese) espr !(c.absen)
  let pr ch x =
    match x with
    | Known l -> Printf.fprintf ch "{%a}" espr l
    | Unkno c -> cpr ch c

  (** Creation of new totality variables *)
  let create =
    let c = ref 0 in
    fun ?(absent=[]) ?(present=[]) () ->
    let x = !c in
    c:=x+1;
    Unkno { uiden = x
          ; lower = ref []
          ; upper = ref []
          ; absen = ref absent
          ; prese = ref present
          }

  let complement l = List.filter (fun x -> not (List.mem x l)) E.all

  let rec present_cts v c =
    let open T in
    if List.mem v !(c.prese) then true
    else if List.mem v !(c.absen) then false
    else
      begin
        c.prese := v :: !(c.prese);
        let f (x, except) =
          List.mem v except || present_cts v x
        in
        assert (List.for_all f !(c.upper));
        true
      end

  let present v t =
    match t with
    | Known l -> List.mem v l
    | Unkno c -> present_cts v c

  let rec absent_cts v c =
    let open T in
    if List.mem v !(c.absen) then true
    else if List.mem v !(c.prese) then false
    else
      begin
        c.absen := v :: !(c.absen);
        let f (x, except) =
          List.mem v except || absent_cts v x
        in
        assert (List.for_all f !(c.lower));
        true
      end

  let absent v t =
    match t with
    | Known l -> not (List.mem v l)
    | Unkno c -> absent_cts v c

  let subset s1 s2 = List.for_all (fun x -> List.mem x s2) s1
  let inter  s1 s2 = List.filter (fun x -> List.mem x s1) s2

  let remassq x l = List.filter (fun (y,_) -> y == x) l

  let rec sub_cts except v w =
    let open T in
    let except_old = try List.assq v !(w.lower) with Not_found -> E.all in
    if subset except_old except then true
    else
      begin
        let except = inter except except_old in
        w.lower := (v, except) :: (remassq v !(w.lower));
        v.upper := (w, except) :: (remassq w !(v.upper));
        List.for_all (fun x -> List.mem x except ||
                                 present_cts x w) !(v.prese) &&
        List.for_all (fun x -> List.mem x except ||
                                 absent_cts x v) !(w.absen)
      end

  (** Definition of the order between two totalities. [sub t1 t2 = true]
    means that a ->_t1 b < a ->_t2 b : the order correspond to the ordre of
    subtyping in the annotated implication: more effects, more programs,
    larger *)
  let sub ?(except=[]) t1 t2 =
    t1 == t2 ||
      match (t1, t2) with
      | (Known l, Known h) ->
         List.for_all (fun x -> List.mem x except || List.mem x h) l
      | (Known l, Unkno v) ->
         List.for_all (fun x -> List.mem x except || present_cts x v) l
      | (Unkno v, Known l) ->
         List.for_all (fun x -> List.mem x except
                                || absent_cts x v) (complement l)
      | (Unkno v, Unkno w) ->
         sub_cts except v w


  let know_sub t1 es =
    match t1 with
    | Known l -> List.for_all (fun x -> List.mem x es) l
    | Unkno v -> List.for_all (fun x -> List.mem x !(v.absen)) (complement es)

  (** Timed protected version *)
  let sub ?(except=[]) t1 t2 = T.pure_test (sub ~except t1) t2

  (** Equality *)
  let eq t1 t2 = sub t1 t2 && sub t2 t1

  let eq t1 t2 = T.pure_test (eq t1) t2

  (* NOTE: can be make stronger *)
  let know_eq t1 t2 =
    match complete t1, complete t2 with
    | Some l1, Some l2 ->
       List.for_all (fun x -> List.mem x l1) l2 &&
         List.for_all (fun x -> List.mem x l2) l1
    | _ -> t1 == t2

  (* Hash *)
  let hash t1 =
    match t1 with
    | Unkno v -> Hashtbl.hash v.uiden
    | Known l -> Hashtbl.hash l

end
