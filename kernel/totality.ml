

type tot = Unk of tot option ref
         | Any | Ter | Tot

let rec norm = function
  | Unk ({ contents = Some t } as v) ->
     let u = norm t in
     if u != t then Timed.(v := Some u);
     u
  | t                             -> t

let new_tot () = Unk (ref None)

let sub t1 t2 =
  let t1 = norm t1 and t2 = norm t2 in
  match (t1, t2) with
  | (Tot   , _     ) -> true
  | (Unk v1, Unk v2) when t1 == t2
                     -> true
  | (Unk v1, t2    ) -> Timed.(v1 := Some t2); true
  | (t1    , Unk v2) -> Timed.(v2 := Some t1); true
  | (_     , Tot   ) -> false
  | (Ter   , _     ) -> true
  | (_     , Ter   ) -> false
  | (Any   , Any   ) -> true

let eq t1 t2 =
  let t1 = norm t1 and t2 = norm t2 in
  match (t1, t2) with
  | (Unk v1, Unk v2) when t1 == t2
                     -> true
  | (Unk v1, t2    ) -> Timed.(v1 := Some t2); true
  | (t1    , Unk v2) -> Timed.(v2 := Some t1); true
  | _                -> t1 = t2

let hash t1 =
  match norm t1 with
  | Unk v -> v := Some Tot; Hashtbl.hash Tot (* FIXME *)
  | t     -> Hashtbl.hash t

let is_term t = sub t Ter

let is_not_tot t = sub Ter t
