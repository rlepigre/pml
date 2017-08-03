type pair<a,b> = ∃ x y:ι, {fst = x ; snd = y} ∈ {fst : a ; snd : b ⋯}
// type pair<a,b> = {fst : a ; snd : b}

val couple : ∀ a b, a ⇒ b ⇒ pair<a,b> = fun x y →
  {fst = x ; snd = y}

val pi1 : ∀ a b, pair<a,b> ⇒ a = fun p → p.fst
val pi2 : ∀ a b, pair<a,b> ⇒ b = fun p → p.snd
val true_pair : ∀a b, ∀p∈pair<a,b>, ∃x y:ι, p ≡ {fst = x ; snd = y} =
  fun p → {}
