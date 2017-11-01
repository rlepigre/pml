

type tot = Unk of { mutable value : tot option }
         | Any | Ter | Tot

let rec norm = function
  | Unk ({ value = Some t } as v) ->
     let u = norm t in
     if u != t then v.value <- Some u;
     u
  | t                             -> t

let new_tot () = Unk { value = None }

let sub t1 t2 =
  let t1 = norm t1 and t2 = norm t2 in
  match (t1, t2) with
  | (Tot   , _     ) -> true
  | (Unk v1, Unk v2) when t1 == t2
                     -> true
  | (Unk v1, t2    ) -> v1.value <- Some t2; true
  | (t1    , Unk v2) -> v2.value <- Some t1; true
  | (_     , Tot   ) -> false
  | (Ter   , _     ) -> true
  | (_     , Ter   ) -> false
  | (Any   , Any   ) -> true

let is_term t = sub t Ter
