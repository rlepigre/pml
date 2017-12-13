include lib.nat
include lib.nat_proofs
include lib.stream

// Axiome du choix intuitionniste
val ac : ∀a,∀b, (∀n∈nat, ∃m∈b, a<n,m>) ⇒
            ∃f∈(nat ⇒ b), ∀n∈nat, ∃v:ι,a<n,v>|v≡f n =
  fun g {
    let a,b such that g : ∀n∈nat, ∃m∈b, a<n,m>;
    let f : nat ⇒ b = fun n { (g n).1 };
    (f, fun n { (g n).2 })
  }

// Below is a too complicated proof of the intuitionnistic ac using streams.
// It demonstrates proving properties with streams.
// and compute g n only once.

val ex : ∀a,∀b, (∀n∈nat, ∃m∈b, a<n,m>) ⇒
           ∃s∈stream<∃n∈nat, ∃m∈b, a<n,m>>, ∀n∈nat, (nth n s).1 ≡ n =
  fun g {
    let a,b such that g : ∀n∈nat, ∃m∈b, a<n,m>;
    let rec fn : nat ⇒ stream<∃n∈nat,∃m∈b, a<n,m>> = fun n _ {
      let hd : ∃n∈nat,∃m∈b, a<n,m> = (n, g n);
      { hd; tl = fn (S[n]) }
    };
    let rec lem : ∀n k∈nat, (nth k (fn n)).1 ≡ add n k = fun n k {
      case k {
        Zero  → let x = g n; //FIXME #28
                use add_n_zero n; qed
        S[k'] → let x = g n; //FIXME #28
                use add_n_succ n k';
                use lem S[n] k'; qed
      }
    };
    let lemz : ∀n∈nat, (nth n (fn Zero)).1 ≡ n = lem Zero;
    (fn Zero, lemz)
  }

val ac : ∀a,∀b, (∀n∈nat, ∃m∈b, a<n,m>) ⇒
            ∃f∈(nat ⇒ b), ∀n∈nat, ∃v:ι,a<n,v>|v≡f n =
  fun g {
    let a,b such that g : ∀n∈nat, ∃m∈b, a<n,m>;
    let sp: ∃s∈stream<∃n∈nat, ∃m∈b, a<n,m>>, ∀m∈nat, (nth m s).1 ≡ m = ex g;
    let (s, lem) = sp;
    let f : nat ⇒ b = fun n { let (n', q) = nth n s; q.1 };
                              // FIXME: (nth n s).2.1 fails
    (f, fun n {
        let (n', q) = nth n s;
        show n' ≡ n using lem n;
        deduce f n ≡ q.1;
        q.2
        })
  }

// Axiome du choix classique, rejected
// val acc : ∀a,∀b, (∀n, n∈nat → ∃m∈b, a<n,m>) ⇒
//             ∃f∈(nat → b), ∀n, n∈nat→ ∃v:ι,a<n,v>|v≡f n =
//   fun g {
//     let a,b such that g : ∀n, n∈nat → ∃m∈b, a<n,m>;
//     let f : nat → b = fun n { (g n).1 };
//     (f, fun n { (g n).2 })
//   }

// Type of classical streams.
type corec cstream<a> = {} → {hd : a; tl : cstream}

// val exc : ∀a,∀b, (∀n, n∈nat → ∃m∈b, a<n,m>) ⇒
//            ∃s∈cstream<∃n∈nat, ∃m∈b, a<n,m>>, ∀n, n∈nat → (nth n s).1 ≡ n =
//   fun g {
//     let a,b such that g : ∀n, n∈nat → ∃m∈b, a<n,m>;
//     let rec fn : nat ⇒ cstream<∃n∈nat,∃m∈b, a<n,m>> = fun n _ {
//       let hd : ∃n∈nat,∃m∈b, a<n,m> = (n, g n);
//       { hd; tl = fn (S[n]) }
//     };
//     let rec lem : ∀n∈nat, ∀k, k∈nat → (nth k (fn n)).1 ≡ add n k = fun n k {
//       case k {
//         Zero  → let x = g n; // fails here
//                 use add_n_zero n; qed
//         S[k'] → let x = g n; // and there
//                 use add_n_succ n k';
//                 use lem S[n] k'; qed
//       }
//     };
//     let lemz : ∀n, n∈nat → (nth n (fn Zero)).1 ≡ n = fun k { lem Zero k };
//        // FIXME, without eta expansion above pml loops
//     (fn Zero, lemz)
//   }

// Compute the list of the first n elements of a stream.
val rec nthc : ∀a, nat ⇒ cstream<a> → a =
  fun n s {
    case n {
           | Zero → (s {}).hd
           | S[k] → nthc k (s {}).tl
    }
  }

// val acc : ∀a,∀b, (∀n, n∈nat → ∃m∈b, a<n,m>) ⇒
//             ∃f∈(nat → b), ∀n, n∈nat→ ∃v:ι,a<n,v>|v≡f n =
//   fun g {
//     let a,b such that g : ∀n, n∈nat → ∃m∈b, a<n,m>;
//     let sp: ∃s∈cstream<∃n∈nat, ∃m∈b, a<n,m>>, ∀m, m∈nat → (nth m s).1 ≡ m = exc g;
//     let (s, lem) = sp;
//     let f : nat → b = fun n { let (n', q) = nthc n s; q.1 };
//                               // FIXME: (nth n s).2.1 fails
//     (f, fun n {
//         let (n', q) = nthc n s;
//         show n' ≡ n using lem n;
//         deduce f n ≡ q.1;
//         q.2
//         })
//   }
