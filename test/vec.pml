include test.nat
include test.list

val rec length : ∀a:ο, list<a> ⇒ nat =
  fun l {
    case l {
      Nil    → zero
      Cns[c] → succ (length c.tl)
    }
  }

type vec<a:ο,s:τ> = ∃l:ι, l∈(list<a> | length l ≡ s)

val vnil : ∀a:ο, vec<a,zero> = nil

val vcns : ∀a:ο,∀s:ι, ∀x∈a, vec<a,s> ⇒ vec<a,S[s]> =
  fun y ls {
    let test : nat = length ls;
    Cns[{hd = y; tl = ls}]
  }

val vcns : ∀a:ο,∀s:ι, ∀x∈a, vec<a,s> ⇒ vec<a,S[s]> =
  fun y ls { Cns[{hd = y; tl = ls}] }

val rec app : ∀a:ο, ∀n1 n2:ι, vec<a,n1> ⇒ vec<a,n2> ⇒ vec<a,add n1 n2> =
  fun l1 l2 {
    case l1 {
      Nil    → l2
      Cns[c] →
        let r = app c.tl l2;
        vcns c.hd r
    }
  }

val app3 : ∀a:ο, ∀n1 n2 n3:ι, vec<a,n1> ⇒ vec<a,n2> ⇒ vec<a,n3>
           ⇒ vec<a,add n1 (add n2 n3)> =
    fun l1 l2 l3 {
       app l1 (app l2 l3)
    }
