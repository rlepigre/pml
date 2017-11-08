(* Part of the code for the pool that is needed in Ast module *)

(** Poll inside terms *)
type v_ptr = { vadr : int; vlnk : lnk Timed.tref }
and  t_ptr = { tadr : int; tlnk : lnk Timed.tref }
and  ptr   = V_ptr of v_ptr | T_ptr of t_ptr
and lnk = Lnk of ptr | Par of ptr list

let cmp : ptr -> ptr -> int = fun p1 p2 ->
  match p1, p2 with
  | V_ptr p1, V_ptr p2 -> p1.vadr - p2.vadr
  | T_ptr p1, T_ptr p2 -> p1.tadr - p2.tadr
  | V_ptr _ , T_ptr _  -> -1
  | T_ptr _ , V_ptr _  ->  1

let eq_ptr p1 p2 = cmp p1 p2 = 0

let rec add_ptr : ptr -> ptr list -> ptr list = fun p l ->
  match l with
  | []    -> [p]
  | q::l' -> match cmp p q with
             | 0 -> l
             | n when n < 0 -> p::l
             | _ -> q::add_ptr p l'

let rec inter_ptr : ptr list -> ptr list -> ptr list = fun l1 l2 ->
  match (l1, l2) with
  | ([]     , _      ) -> []
  | (_      , []     ) -> []
  | (p1::l1', p2::l2') -> match cmp p1 p2 with
                          | 0  -> p1 :: inter_ptr l1' l2'
                          | n when n < 0 -> inter_ptr l1' l2
                          | _ -> inter_ptr l1 l2'

let rec union_ptr : ptr list -> ptr list -> ptr list = fun l1 l2 ->
  match (l1, l2) with
  | ([]     , _      ) -> l2
  | (_      , []     ) -> l1
  | (p1::l1', p2::l2') -> match cmp p1 p2 with
                          | 0  -> p1 :: union_ptr l1' l2'
                          | n when n < 0 -> p1 :: union_ptr l1' l2
                          | _ -> p2 :: union_ptr l1 l2'

(** Module for pointers on a value node of the graph. *)
module VPtr =
  struct
    type t = v_ptr
    let compare i j = i.vadr - j.vadr
    let print ch i = Printf.fprintf ch "%i" i.vadr
  end

module VPtrMap = Map.Make(VPtr)
module VPtrSet = Set.Make(VPtr)

(** Module for pointers on a term node of the graph. *)
module TPtr =
  struct
    type t = t_ptr
    let compare i j = i.tadr - j.tadr
    let print ch i = Printf.fprintf ch "%i" i.tadr
  end

module TPtrMap = Map.Make(TPtr)

(** Module for pointers on a term or a value node of the graph. *)
module Ptr =
  struct
    type t = ptr

    let compare p1 p2 =
      match (p1, p2) with
      | (V_ptr _ , T_ptr _ ) -> -1
      | (T_ptr _ , V_ptr _ ) -> 1
      | (V_ptr p1, V_ptr p2) -> VPtr.compare p1 p2
      | (T_ptr p1, T_ptr p2) -> TPtr.compare p1 p2

    let print ch p =
      match p with
      | V_ptr p -> VPtr.print ch p
      | T_ptr p -> TPtr.print ch p
  end
module PtrMap = Map.Make(Ptr)
module PtrSet = Set.Make(Ptr)
module TPtrSet = Set.Make(TPtr)

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

let ptr_par : Ptr.t -> Timed.Time.t -> Ptr.t list = fun p time ->
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

let ptr_add_par : Ptr.t -> Ptr.t ->  Timed.Time.t -> Timed.Time.t =
  fun p1 p2 time ->
    let ps = add_ptr p1 (ptr_par p2 time) in
    match p2 with
    | V_ptr vp -> Timed.set time vp.vlnk (Par ps)
    | T_ptr tp -> Timed.set time tp.tlnk (Par ps)

let ptr_add_pars : Ptr.t list -> Ptr.t ->  Timed.Time.t -> Timed.Time.t =
  fun ps p2 time ->
    let ps = union_ptr ps (ptr_par p2 time) in
    match p2 with
    | V_ptr vp -> Timed.set time vp.vlnk (Par ps)
    | T_ptr tp -> Timed.set time tp.tlnk (Par ps)
