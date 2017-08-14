
//def pair<a:ο,b:ο> = ∃v:ι, v ∈ ({ fst : a; snd : b } |
//   v ≡ (let fst = v.fst in
//        let snd = v.snd in { fst = fst; snd = snd }))
// TODO: test this bad (too complex) definition
// the proof below does not work with this def

def pair<a:ο,b:ο> = ∃v w:ι, { fst = v; snd = w } ∈ { fst : a; snd : b }

val swap : ∀a b:ο, pair<a,b> ⇒ pair<b,a> =
  fun x {
    let fst = x.fst in
    let snd = x.snd in
    { fst = snd; snd = fst }
  }

val swap_idempotent :∀a b:ο, ∀x∈pair<a,b>, swap (swap x) ≡ x = fun x { {} }
