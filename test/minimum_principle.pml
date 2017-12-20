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

val rec fn : ∀f∈(nat ⇒ nat), ∀n∈nat, ∀q∈(nat | q ≡ f n),
    (∀n∈ nat, min<n,f> → bot) → bot =
  fun f n q k {
    let o such that q : nat^(o+1);
    k (n:nat) (fun p {
        let fp = f p;
        case leq_size (q:nat^(o+1)) fp {
          InL     → {}
          InR[fp] → fn f p fp k
        }} : min<n,f>)
  }

type umin<n,f> = ∀p, p ∈ nat ↝ leq (f n) (f p)

val rec gn : ∀f∈(nat ⇒ nat), ∀n∈nat,
    (∀n∈ nat, umin<n,f> → bot) ↝ bot =
  fun f n k {
    k (n:nat) (fun p { gn f p k } : umin<n,f>)
  }

// It would be nice to prove fn ≡ gn ⋯
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
      fn f Zero (f Zero) k
    }
  }

val test : ∀f:ι, f∈(nat ⇒ nat) ⇒ ∃n∈nat, leq (f n) (f (succ (mul 2 n))) =
  fun f {
    delim {
      set auto 0 5;
      let (n,p) = minimum_principle f;
      println_nat n; //print intermediate results
      (n, p (succ (mul 2 n)))
    }
  }

val max : nat ⇒ nat ⇒ nat = fun x y { if leq x y { y } else { x } }
val abssub : nat ⇒ nat ⇒ nat = fun x y { max (x - y) (y - x) }
val f_alex : nat ⇒ nat = fun n { abssub n 1000 }

val test1 : ∃n, n∈nat | leq (f_alex n) (f_alex (succ (2 * n))) =
  (test f_alex).1
val test2 : {} = println_nat test1
