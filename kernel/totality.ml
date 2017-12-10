(** Second time for uvar and totality *)
module UTimed = Timed.Make(Timed.Time)

type tot = Unk of int * tot option ref
         | Any | Ter | Tot
         | Max of tot * tot

let rec norm = function
  | Unk (_, ({ contents = Some t } as v)) ->
     let u = norm t in
     if u != t then UTimed.(v := Some u);
     u
  | t -> t

let new_tot =
  let c = ref 0 in
  fun () -> let x = !c in c:=x+1; Unk (x, ref None)

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

let max t1 t2 = match (norm t1, norm t2) with
  | (Tot, t) | (t, Tot) -> t
  | (Any, _) | (_, Any) -> Any
  | (t, u) when t == u -> t
  | (t, u) -> Max(t,u)

let sub t1 t2 = UTimed.pure_test (sub t1) t2

let eq t1 t2 =
  let t1 = norm t1 and t2 = norm t2 in
  match (t1, t2) with
  | (Unk(_,v1), Unk(_,v2)) when t1 == t2
                           -> true
  | (Unk(_,v1), t2       ) -> UTimed.(v1 := Some t2); true
  | (t1       , Unk(_,v2)) -> UTimed.(v2 := Some t1); true
  | _                      -> sub t1 t2 && sub t2 t1

let eq t1 t2 = UTimed.pure_test (eq t1) t2

let hash t1 =
  match norm t1 with
  | Unk(i,v) -> Hashtbl.hash i
  | t        -> Hashtbl.hash t

let is_term t = UTimed.pure_test (sub t) Ter

let is_tot t = UTimed.pure_test (sub t) Tot

let is_not_tot t = UTimed.pure_test (sub Ter) t

let rec know_tot t = match norm t with
  | Tot -> true
  | Max(t1,t2) -> know_tot t1 && know_tot t2
  | _   -> false
