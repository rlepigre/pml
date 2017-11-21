type rec nat = [ Z ; S of nat ]

val zero : nat = Z
val succ : nat ⇒ nat = fun n { S[n] }
val one  : nat = succ zero
val two  : nat = succ one

def add0 =
  fix add { fun n m {
    case n {
      Z    → m
      S[p] → let _ = add p m;
             S[add p m] // succ (add p m) fails ?
                        // it should be exactly the same
    }
  }}

val add : ∀n m∈nat, ∃v:ι, v∈nat | v ≡ add0 n m = add0

val test : add ≡ add0 = {} // did not work before 23/3/2017 patch

// A variant that works
def add1 =
  fix add { fun n m {
    case n {
      Z    → m
      S[p] → let _ = add p m;
             succ (add p m)
    }
  }}

val addbis : ∀n m∈nat, ∃v:ι, v∈nat | v ≡ add1 n m = add1

val rec add_asso : ∀n m q∈nat, add n (add m q) ≡ add (add n m) q =
  fun n m q {
    let _ = add m q;
    case n {
      Z    → {}
      S[p] →
        let _ = add p (add m q);
        let _ = add p m;
        let _ = add (add p m) q;
        deduce add n (add m q) ≡ succ (add p (add m q));
        deduce add (add n m) q ≡ succ (add (add p m) q);
        show add p (add m q) ≡ add (add p m) q using add_asso p m q
    }
  }
