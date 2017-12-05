include lib.either
include lib.nat
include lib.nat_proofs

type min<n,f> = ∀p, p ∈ nat → leq (f n) (f p)

type bot = ∀x:ο,x

val rec leq_size : ∀o, ∀m∈nat^(o+1), ∀n∈nat, either<leq m n, n∈nat^o> =
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
    let o such that q : nat^(o+1);
    k (n:nat) (fun p {
        use total f p;
        case leq_size (q:nat^(o+1)) (f p) {
          InL     → {}
          InR[fp] → fn f p fp k
        }} : min<n,f>)
  }

val unsafe gn : ∀f∈(nat ⇒ nat), ∀n∈nat,
    (∀n∈ nat, min<n,f> → bot) → bot =
  fun f n k {
    k (n:nat) (fun p { gn f p k } : min<n,f>)
  }

// val lemma : ∀f∈(nat ⇒ nat), ∀n∈nat, ∀q∈(nat | q ≡ f n),
//               ∀k∈(∀n∈ nat, min<n,f> → bot), fn f n q k ≡ gn f n k =
//   fun f n q k {
//     let o such that q : nat^(o+1);
//     k (n:nat) (fun p {
//         use total f p;
//         case leq_size (q:nat^(o+1)) (f p) {
//           InL     → {}
//           InR[fp] → fn f p fp k
//         }} : min<n,f>)
//   }

val minimum_principle : ∀f:ι, f∈(nat ⇒ nat) → ∃n∈nat, min<n,f> =
  fun f {
    save s {
      let k : ∀n∈ nat, min<n,f> → bot =
        fun n mi { restore s (n, mi) };
      use total f Zero;
      fn f Zero (f Zero) k
    }
  }

val test : ∀f:ι, f∈(nat ⇒ nat) ⇒ ∃n∈nat, leq (f n) (f (succ (mul u2 n))) =
  fun f {
    delim {
      let (n,p) = minimum_principle f;
      //println_nat n;
      use total (mul u2) n;
      (n, p (succ (mul u2 n)))
    }
  }

val max : nat ⇒ nat ⇒ nat = fun x y { if leq x y { y } else { x } }
val abssub : nat ⇒ nat ⇒ nat = fun x y { max (minus x y) (minus y x) }
val f_alex : nat ⇒ nat = fun n { abssub n u1000 }
val test1 : {} = println_nat (test f_alex).1
