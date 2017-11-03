include lib.either
include lib.nat
include lib.nat_proofs

type min<n,f> = ∀p, p ∈ nat → leq (f n) (f p) ≡ true

type bot = ∀x:ο,x

type snat<o> = μ_o nat, [ Zero ; S of nat ]

val rec leq_size : ∀o, ∀m∈snat<o+1>, ∀n∈nat, either<leq m n ≡ true, n∈snat<o>> =
  fun m n {
    case m {
      Zero → case n {
          Zero → InL
          S[n] → InL
        }
      S[m] →
        case n {
          Zero → InR[Zero]
          S[n] →
            case m {  // case for n because leq use compare
              Zero  → case n { Zero → InL | S[_] → InL}
              S[m'] →
                case leq_size S[m'] n {
                  InL    → InL
                  InR[p] → InR[S[p]]
                  }
              }
          }
      }
  }

val total : ∀a b, ∀f∈a⇒b, ∀x∈a, ∃v:ι, v ∈ b | v ≡ f x =
  fun f x { let y = f x; y }


val rec fn : ∀f∈(nat ⇒ nat), ∀n∈nat, ∀q∈(nat | q ≡ f n),
    (∀n∈ nat, min<n,f> → bot) → bot =
  fun f n q k {
    let o such that q : snat<o+1>;
    k (n:nat) (fun p {
        use total f p;
        case leq_size (q:snat<o+1>) (f p) {
          InL     → {}
          InR[fp] → fn f p fp k
        }} : min<n,f>)
  }

val minimum_principle : ∀f:ι, f∈(nat ⇒ nat) → ∃n∈nat, min<n,f> =
  fun f {
    save s {
      let k : ∀n∈ nat, min<n,f> → bot = fun n mi { restore s (n, mi) };
      use total f Zero;
      fn f Zero (f Zero) k
    }
  }
