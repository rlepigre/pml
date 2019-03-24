include lib.nat

type rec list⟨a⟩ = [ Nil; Cns of { hd : a; tl : list⟨a⟩ }  ]

val nil : ∀a:ο, list⟨a⟩ = Nil
val cns : ∀a:ο, a ⇒ list⟨a⟩ ⇒ list⟨a⟩ =
  fun e l { Cns[{ hd = e; tl = l }] }

val rec length : ∀a:ο, list⟨a⟩ ⇒ nat =
  fun l {
    case l {
      Nil[_] → zero
      Cns[c] → succ (length c.tl)
    }
  }

type vec⟨a:ο,s:τ⟩ = ∃l:ι, l∈(list⟨a⟩ | length l ≡ s)
// The fact that s:τ is very important
// The position of the partenthesis is important

val vnil : ∀a:ο, vec⟨a,zero⟩ = nil

val vcns : ∀a:ο,∀s:ι, ∀x∈a, vec⟨a,s⟩ ⇒ vec⟨a,succ s⟩ =
  fun y ls { Cns[{hd= y;tl= ls}] }

val total : ∀a b, ∀f∈a⇒b, ∀x∈a, ∃v:ι, v ∈ b | v ≡ f x =
  fun f x { let y = f x; y }

val rec app : ∀a:ο, ∀n1 n2:ι, vec⟨a,n1⟩ ⇒ vec⟨a,n2⟩ ⇒ vec⟨a,add n1 n2⟩ =
  fun l1 l2 {
    case l1 {
      Nil    → l2
      Cns[c] →
        use total length c.tl;
        let r = app c.tl l2;
        use total length r;
        vcns c.hd r
    }
  }

val app3 : ∀a:ο, ∀n1 n2 n3:ι, vec⟨a,n1⟩ ⇒ vec⟨a,n2⟩ ⇒ vec⟨a,n3⟩
           ⇒ vec⟨a,add n1 (add n2 n3)⟩ =
    fun l1 l2 l3 {
       use total (add (length l2)) (length l3);
       app l1 (app l2 l3)
    }
