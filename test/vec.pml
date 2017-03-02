include test.nat
include test.list

val length : ∀a:ο, list<a> ⇒ nat = fix fun length l →
  case l of
  | Nil[] → zero
  | Cns[c] → succ (length c.tl)

type vec<a:ο,s:ι> = ∃l:ι, l∈(list<a> | length l ≡ s)

val vnil : ∀a:ο, vec<a,zero> = nil

val vcns : ∀a:ο,∀s:ι, ∀x∈a, vec<a,s> ⇒ vec<a,S[s]> =
   Λa:ο. Λs:ι. fun y ls →
    let deduce : s ≡ length ls = {} in
    let test : nat = length ls in
    let deduce : length (cns y ls) ≡ S[s] = {} in
    Cns[{hd = y; tl = ls}]

val vcns : ∀a:ο,∀s:ι, ∀x∈a, vec<a,s> ⇒ vec<a,S[s]> =
   Λa:ο. Λs:ι. fun y ls →
    Cns[{hd = y; tl = ls}]
