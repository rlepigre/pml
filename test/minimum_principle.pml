include lib.nat
include lib.nat_proofs

type min<n,f> = ∀p ∈ nat, leq (f n) (f p) ≡ true

def total<f,a:ο> = ∀x∈a, ∃w:ι, f x ≡ w

type bot = ∀x:ο,x

type snat<o> = μo nat [ Z ; S of nat ]

val leq_size : ∀o, ∀m∈snat<o+1>, ∀n∈nat, [ Ok of leq m n ≡ true ; Bad of n∈snat<o> ]
  = fun m n →
      {- case m  -}

// val rec fn : ∀o, ∀f∈(nat ⇒ nat), total<f,nat> ⇒ ∀n∈nat, ∀q∈(snat<o> | q ≡ f n),
//                        (∀n∈ nat, min<n,f> ⇒ bot) ⇒ bot =
//     fun f ft n q k →
//       k (n:nat) ((fun p →
//         use ft p;
//         use leq_total q (f p);
//         case leq_size q (f p) {
//           Ok      → {}
//           Bad[fp] → fn f ft p fp k
//         }) : min<n,f>)


//val minimum_principle : ∀f∈(nat ⇒ nat), total<f,nat> ⇒ ∃n:ι, min<n,f> =
//  fun f ft → save ct →
