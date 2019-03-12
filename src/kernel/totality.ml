(** This module implements the totality decoration for arrow types *)

(** Second time for uvar and totality We need to level of time because
backtracking in the pool should not backtrack unification variables that we
have in Ast and in this module *)
module UTimed = Timed.Make(Timed.Time)

(** Ast of these decoration *)
type tot =
  | Any (** may be classical and/or non terminating *)
  | Ter (** classical logic is possible, but termination is ensured *)
  | Tot (** total: the function is terminating and returning a value *)
  | Max of tot * tot (** maximum: used to type-check case analysis *)
  | Unk of int * tot option ref (** unification variables for totality *)

(** Normalisation, like in union find data structure *)
let rec norm = function
  | Unk (_, ({ contents = Some t } as v)) ->
     let u = norm t in
     if u != t then UTimed.(v := Some u);
     u
  | t -> t

(** Creation of new totality variables *)
let new_tot =
  let c = ref 0 in
  fun () -> let x = !c in c:=x+1; Unk (x, ref None)

(** Definition of the order between two totalities. [sub t1 t2 = true] means
    that a ->_t1 b < a ->_t2 b : the order correspond to the ordre of
    subtyping in the annotated implication *)
let rec sub t1 t2 =
  let t1 = norm t1 and t2 = norm t2 in
  match (t1, t2) with
  | (Tot      , _        ) -> true
  | (Unk(_,v1), Unk(_,v2)) when t1 == t2
                           -> true
  | (Unk(_,v1), t2       ) -> UTimed.(v1 := Some t2); true
  | (t1       , Unk(_,v2)) -> UTimed.(v2 := Some t1); true
  | (Max(t,u) , t2       ) -> sub t t2 && sub u t2
  | (t1       , Max(t,u) ) -> UTimed.pure_test (sub t1) t || sub t1 u
  | (_        , Tot      ) -> false
  | (Ter      , _        ) -> true
  | (_        , Ter      ) -> false
  | (Any      , Any      ) -> true

(** Timed protected version *)
let sub t1 t2 = UTimed.pure_test (sub t1) t2

(** optimized maximum *)
let max t1 t2 = match (norm t1, norm t2) with
  | (Tot, t) | (t, Tot) -> t
  | (Any, _) | (_, Any) -> Any
  | (t, u) when t == u -> t
  | (t, u) -> Max(t,u)

(** Equality *)
let eq t1 t2 =
  let t1 = norm t1 and t2 = norm t2 in
  match (t1, t2) with
  | (Unk(_,v1), Unk(_,v2)) when t1 == t2
                           -> true
  | (Unk(_,v1), t2       ) -> UTimed.(v1 := Some t2); true
  | (t1       , Unk(_,v2)) -> UTimed.(v2 := Some t1); true
  | _                      -> sub t1 t2 && sub t2 t1

let eq t1 t2 = UTimed.pure_test (eq t1) t2

(* Hash *)
let hash t1 =
  match norm t1 with
  | Unk(i,v) -> Hashtbl.hash i
  | t        -> Hashtbl.hash t

(* Other derived tests *)
let is_term t = UTimed.pure_test (sub t) Ter

let is_tot t = UTimed.pure_test (sub t) Tot

(* A test for totality that does not instanciate *)
let rec know_tot t = match norm t with
  | Tot -> true
  | Max(t1,t2) -> know_tot t1 && know_tot t2
  | _   -> false
