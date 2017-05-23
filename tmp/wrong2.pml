type snat<a:κ> = μa nat [ Z ; S of nat ]
type nat = snat<∞>

val rec id_nat : ∀a:κ, snat<a> ⇒ snat<a> = fun n →
  case n {
    | Z[_] → Z[]
    | S[p] → id_nat n
  }
