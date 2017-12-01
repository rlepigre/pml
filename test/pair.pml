
def pair<a:ο,b:ο> = ∃v w:ι, { fst = v; snd = w } ∈ { fst : a; snd : b }

val swap : ∀a b:ο, pair<a,b> ⇒ pair<b,a> =
  fun x {
    let fst = x.fst;
    let snd = x.snd;
    { fst = snd; snd = fst }
  }

val swap_idempotent :∀a b:ο, ∀x∈pair<a,b>, swap (swap x) ≡ x = fun x { {} }
