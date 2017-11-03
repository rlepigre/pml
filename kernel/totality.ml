

type tot = Unk of int * tot option ref
         | Any | Ter | Tot

let rec norm = function
  | Unk (_, ({ contents = Some t } as v)) ->
     let u = norm t in
     if u != t then Timed.(v := Some u);
     u
  | t -> t

let new_tot =
  let c = ref 0 in
  fun () -> let x = !c in c:=x+1; Unk (x, ref None)

let sub t1 t2 =
  let t1 = norm t1 and t2 = norm t2 in
  match (t1, t2) with
  | (Tot      , _        ) -> true
  | (Unk(_,v1), Unk(_,v2)) when t1 == t2
                           -> true
  | (Unk(_,v1), t2       ) -> Timed.(v1 := Some t2); true
  | (t1       , Unk(_,v2)) -> Timed.(v2 := Some t1); true
  | (_        , Tot      ) -> false
  | (Ter      , _        ) -> true
  | (_        , Ter      ) -> false
  | (Any      , Any      ) -> true

let sub t1 t2 = Timed.pure_test (sub t1) t2

let eq t1 t2 =
  let t1 = norm t1 and t2 = norm t2 in
  match (t1, t2) with
  | (Unk(_,v1), Unk(_,v2)) when t1 == t2
                           -> true
  | (Unk(_,v1), t2       ) -> Timed.(v1 := Some t2); true
  | (t1       , Unk(_,v2)) -> Timed.(v2 := Some t1); true
  | _                      -> t1 = t2

let eq t1 t2 = Timed.pure_test (eq t1) t2

let hash t1 =
  match norm t1 with
  | Unk(i,v) -> Hashtbl.hash i
  | t        -> Hashtbl.hash t

let is_term t = Timed.pure_test (sub t) Ter

let is_not_tot t = Timed.pure_test (sub Ter) t

let know_tot t = match norm t with
  | Tot -> true
  | _   -> false
