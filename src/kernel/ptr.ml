module A = Assoc

(** Part of the code for the pool (equiv.ml) that is needed in Ast module.
    We need it in ast because we retain pointer in the pool in the ast to
    avoid going back and forth between Ast and Equiv representation. *)

(** This data type is the key for the parent data structure. For instance,
    the key [KT_Appl `Left] for a node [n] indexes all the parents that uses
    [n] as a left son of an application. *)
type par_key =
  | KV_LAbs of int
  | KV_Cons of A.key
  | KV_Reco of A.key
  | KV_HApp of int
  | KT_Valu
  | KT_Appl of [`Left|`Right]
  | KT_MAbs of int
  | KT_Name
  | KT_Delm
  | KT_Proj of A.key
  | KT_Case of (A.key * int) option (* None for the main value *)
  | KT_FixY of int
  | KT_HApp of int

let is_head = function
  | KT_Appl _
  | KT_Proj _
  | KT_Case None
  | KT_FixY _
  | KT_Name      -> true
  | _            -> false

module Par_key = struct
  type t = par_key
  let compare = compare
end
module MapKey = Map.Make(Par_key)

(** This is to store a t_node/v_node in the t_ptr/v_ptr record below, but as
    these are defined in Equiv.ml, we use modern OCaml to solve this issue *)
type _ ty = ..

type dp = DP : 'a ty * 'a -> dp | Dum

(** Here are the main type definitions *)
module rec Ptr : sig
  (** record for values *)
  type v_ptr = { vadr : int            (** uid *)
               ; vlnk : lnk Timed.tref (** link in the union find structure *)
               ; vval : dp             (** the v_node (see equiv.ml) *)
               ; bs : bool Timed.tref }(** true if we know it is not box *)
  and  t_ptr = { tadr : int            (** uid *)
               ; tlnk : lnk Timed.tref (** link in the union find structure *)
               ; tval : dp             (** the t_node (see equiv.ml) *)
               ; ns : bool Timed.tref  (** was normalised *)
               ; fs : bool Timed.tref  (** free : occur not under binders *) }
  (** ptr: a v_ptr or a t_ptr *)
  and  ptr   = V_ptr of v_ptr | T_ptr of t_ptr
  (** link for the union find, for roots, we store the parent map *)
  and lnk = Lnk of ptr | Par of par_map
  and par_map = PtrSet.t MapKey.t


  type t = ptr
  val compare : ptr -> ptr -> int
  val print : out_channel -> ptr -> unit
end = struct
  type v_ptr = { vadr : int; vlnk : lnk Timed.tref; vval : dp
               ; bs : bool Timed.tref }
  and  t_ptr = { tadr : int; tlnk : lnk Timed.tref; tval : dp
               ; ns : bool Timed.tref; fs : bool Timed.tref }
  and  ptr   = V_ptr of v_ptr | T_ptr of t_ptr
  and lnk = Lnk of ptr | Par of par_map
  and par_map = PtrSet.t MapKey.t

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

(** export types *)
type v_ptr   = Ptr.v_ptr
type t_ptr   = Ptr.t_ptr
type   ptr   = Ptr.ptr
type par_map = Ptr.par_map

let eq_ptr p1 p2 = Ptr.compare p1 p2 = 0

let add_ptr_key k p m =
  let old = try MapKey.find k m with Not_found -> PtrSet.empty in
  MapKey.add k (PtrSet.add p old) m

(** Test is a ptr is a union find root *)
let not_lnk : Ptr.t -> Timed.Time.t -> bool = fun p time ->
  let open Ptr in
  match p with
    | V_ptr vp ->
     begin
       match Timed.get time vp.vlnk with
       | Par _ -> true
       | Lnk x -> false
     end
  | T_ptr tp ->
     begin
       match Timed.get time tp.tlnk with
       | Par _ -> true
       | Lnk x -> false
     end

(** get the next element in the union find, raise Not_found if root *)
let ptr_get : Ptr.t -> Timed.Time.t -> Ptr.t = fun p time ->
  let open Ptr in
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

(** set a link in the union find data structure *)
let ptr_set : Ptr.t -> Ptr.t -> Timed.Time.t -> Timed.Time.t = fun p q time ->
  let open Ptr in
  match p with
  | V_ptr vp -> Timed.set time vp.vlnk (Lnk q)
  | T_ptr tp -> Timed.set time tp.tlnk (Lnk q)

(** get the parent of a root of the union find data structure *)
let ptr_par : Ptr.t -> Timed.Time.t -> par_map = fun p time ->
  let open Ptr in
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

(** Adds one parent to a root *)
let ptr_add_par : par_key -> Ptr.t -> Ptr.t ->  Timed.Time.t -> Timed.Time.t =
  fun k p1 p2 time ->
    let open Ptr in
    let ps = add_ptr_key k p1 (ptr_par p2 time) in
    match p2 with
    | V_ptr vp -> Timed.set time vp.vlnk (Par ps)
    | T_ptr tp -> Timed.set time tp.tlnk (Par ps)

(** Adds multiple parents to a root *)
let ptr_union_pars : par_map -> Ptr.t ->  Timed.Time.t -> Timed.Time.t =
  fun ps p2 time ->
    let open Ptr in
    let f _ x y = Some (PtrSet.union x y) in
    let ps = MapKey.union f ps (ptr_par p2 time) in
    match p2 with
    | V_ptr vp -> Timed.set time vp.vlnk (Par ps)
    | T_ptr tp -> Timed.set time tp.tlnk (Par ps)

type Pos.user += NPtr of ptr | UPtr of ptr | BPtr of ptr * ptr | EPtr of v_ptr
