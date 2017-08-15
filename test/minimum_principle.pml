include lib.either
include lib.nat
include lib.nat_proofs

type min<n,f> = ∀p ∈ nat, leq (f n) (f p) ≡ true

def total<f,a:ο> = ∀x∈a, ∃w:ι, f x ≡ w

type bot = ∀x:ο,x

type snat<o> = μo nat [ Z ; S of nat ]

val rec leq_size : ∀o, ∀m∈snat<o+1>, ∀n∈nat, either<leq m n ≡ true, n∈snat<o>> =
  fun m n {
    case m {
      Z →
        case n {
            Z    → InL
          S[n] → InL
        }
      S[m] →
        case n {
            Z  → case m { Z → InR[Z] | S[_] → InR[Z] }
          S[n] → // case for m because of o > 0 is needed
                 case m {  // case for n because leq use compare
                   Z     → case n { Z → InL | S[_] → InL}
                   S[m'] →
                     case leq_size S[m'] n {
                       InL    → InL
                       InR[p] → InR[S[p]]
                     }
                 }
         }
    }
 }

// val rec fn : ∀o, ∀f∈(nat ⇒ nat), total<f,nat> ⇒ ∀n∈nat, ∀q∈(snat<o> | q ≡ f n),
//                        (∀n∈ nat, min<n,f> ⇒ bot) ⇒ bot =
//     fun f ft n q k →
//       k (n:nat) ((fun p →
//         use ft p;
//         use leq_total q (f p);
//         case leq_size q (f p) {
//           InL     → {}
//           InR[fp] → fn f ft p fp k
//         }) : min<n,f>)


//val minimum_principle : ∀f∈(nat ⇒ nat), total<f,nat> ⇒ ∃n:ι, min<n,f> =
//  fun f ft → save ct →
