type snat⟨a:κ⟩ = μ_a nat, [ Z ; S of nat ]
type nat = snat⟨∞⟩

// Rightfully fails.

//val rec id_nat : ∀a:κ, snat⟨a⟩ ⇒ snat⟨a⟩ =
//  fun n { id_nat n }

// Also fails rightfully.

//val rec id_nat : ∀a:κ, snat⟨a⟩ ⇒ snat⟨a⟩ =
//  fun n {
//    case n {
//      Z[_] → Z
//      S[p] → id_nat n
//    }
//  }
