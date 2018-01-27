// Either type.
type either⟨a,b⟩ = [InL of a ; InR of b]

val inl : ∀a b, a ⇒ either⟨a,b⟩ = fun x { InL[x] }
val inr : ∀a b, b ⇒ either⟨a,b⟩ = fun x { InR[x] }

val gather : ∀a b c, (a ⇒ c) ⇒ (b ⇒ c) ⇒ either⟨a,b⟩ ⇒ c =
  fun f g e {
    case e {
      InL[x] → f x
      InR[x] → g x
    }
  }

val map_either : ∀a b c d, (a ⇒ c) ⇒ (b ⇒ d) ⇒ either⟨a,b⟩ ⇒ either⟨c,d⟩ =
  fun f g e {
    case e {
      InL[x] → InL[f x]
      InR[x] → InR[g x]
    }
  }
