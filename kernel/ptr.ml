module A = Assoc

(* Part of the code for the pool that is needed in Ast module *)

type par_key =
  | KV_LAbs of int
  | KV_Cons of A.key
  | KV_Reco of A.key
  | KV_HApp of int
  | KT_Valu
  | KT_Appl of [`Left|`Right]
  | KT_MAbs of int
  | KT_Name
  | KT_Proj of A.key
  | KT_Case of (A.key * int) option (* None for the main value *)
  | KT_FixY of int option
  | KT_HApp of int

module Par_key = struct
  type t = par_key
  let compare = compare
end
module MapKey = Map.Make(Par_key)

(** Poll inside terms *)

module rec Ptr : sig
  type v_ptr = { vadr : int; vlnk : lnk Timed.tref }
  and  t_ptr = { tadr : int; tlnk : lnk Timed.tref }
  and  ptr   = V_ptr of v_ptr | T_ptr of t_ptr
  and lnk = Lnk of ptr | Par of PtrSet.t  MapKey.t

  type t = ptr
  val compare : ptr -> ptr -> int
  val print : out_channel -> ptr -> unit
end = struct
  type v_ptr = { vadr : int; vlnk : lnk Timed.tref }
  and  t_ptr = { tadr : int; tlnk : lnk Timed.tref }
  and  ptr   = V_ptr of v_ptr | T_ptr of t_ptr
  and lnk = Lnk of ptr | Par of PtrSet.t  MapKey.t

  type t = ptr

  let compare : ptr -> ptr -> int = fun p1 p2 ->
    match p1, p2 with
    | V_ptr p1, V_ptr p2 -> p1.vadr - p2.vadr
    | T_ptr p1, T_ptr p2 -> p1.tadr - p2.tadr
    | V_ptr _ , T_ptr _  -> -1
    | T_ptr _ , V_ptr _  ->  1

  let print ch p =
    match p with
    | V_ptr p -> VPtr.print ch p
    | T_ptr p -> TPtr.print ch p

end

and PtrSet : Set.S with type elt = Ptr.t = Set.Make(Ptr)

(** Module for pointers on a value node of the graph. *)
and VPtr : sig
    type t = Ptr.v_ptr
    val compare : Ptr.v_ptr -> Ptr.v_ptr -> int
    val print : out_channel -> Ptr.v_ptr -> unit
  end = struct
    type t = Ptr.v_ptr
    let compare i j = i.Ptr.vadr - j.Ptr.vadr
    let print ch i = Printf.fprintf ch "%i" i.Ptr.vadr
  end

(** Module for pointers on a term node of the graph. *)
and TPtr : sig
    type t = Ptr.t_ptr
    val compare : Ptr.t_ptr -> Ptr.t_ptr -> int
    val print : out_channel -> Ptr.t_ptr -> unit
  end =
  struct
    type t = Ptr.t_ptr
    let compare i j = i.Ptr.tadr - j.Ptr.tadr
    let print ch i = Printf.fprintf ch "%i" i.Ptr.tadr
  end

module VPtrMap = Map.Make(VPtr)
module VPtrSet = Set.Make(VPtr)
module TPtrMap = Map.Make(TPtr)
module PtrMap = Map.Make(Ptr)
module TPtrSet = Set.Make(TPtr)

include Ptr

let cmp = compare

let eq_ptr p1 p2 = cmp p1 p2 = 0

let add_ptr_key k p m =
  let old = try MapKey.find k m with Not_found -> PtrSet.empty in
  MapKey.add k (PtrSet.add p old) m

let ptr_get : Ptr.t -> Timed.Time.t -> Ptr.t = fun p time ->
  match p with
  | V_ptr vp ->
     begin
       match Timed.get time vp.vlnk with
       | Par _ -> raise Not_found
       | Lnk x -> x
     end
  | T_ptr tp ->
     begin
       match Timed.get time tp.tlnk with
       | Par _ -> raise Not_found
       | Lnk x -> x
     end

let ptr_set : Ptr.t -> Ptr.t -> Timed.Time.t -> Timed.Time.t = fun p q time ->
  match p with
  | V_ptr vp -> Timed.set time vp.vlnk (Lnk q)
  | T_ptr tp -> Timed.set time tp.tlnk (Lnk q)

let ptr_par : Ptr.t -> Timed.Time.t -> PtrSet.t MapKey.t = fun p time ->
   match p with
   | V_ptr vp ->
     begin
       match Timed.get time vp.vlnk with
       | Par l -> l
       | Lnk x -> assert false
     end
   | T_ptr tp ->
     begin
       match Timed.get time tp.tlnk with
       | Par l -> l
       | Lnk x -> assert false
     end

let ptr_add_par : par_key -> Ptr.t -> Ptr.t ->  Timed.Time.t -> Timed.Time.t =
  fun k p1 p2 time ->
    let ps = add_ptr_key k p1 (ptr_par p2 time) in
    match p2 with
    | V_ptr vp -> Timed.set time vp.vlnk (Par ps)
    | T_ptr tp -> Timed.set time tp.tlnk (Par ps)


let ptr_union_pars : PtrSet.t MapKey.t -> Ptr.t ->  Timed.Time.t -> Timed.Time.t =
  fun ps p2 time ->
    let f _ x y = Some (PtrSet.union x y) in
    let ps = MapKey.union f ps (ptr_par p2 time) in
    match p2 with
    | V_ptr vp -> Timed.set time vp.vlnk (Par ps)
    | T_ptr tp -> Timed.set time tp.tlnk (Par ps)
