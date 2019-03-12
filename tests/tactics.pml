type rec nat = [ Zero ; Succ of nat ]

val rec add : nat ⇒ nat ⇒ nat =
  fun n m {
    case n {
      Zero    → m
      Succ[k] → Succ[add k m]
    }
  }

val rec mul : nat ⇒ nat ⇒ nat =
  fun n m {
    case n {
      Zero    → Zero
      Succ[k] → add m (mul k m)
    }
  }

val add_zero_v : ∀v:ι,   add Zero v ≡ v    = {}
val mul_zero_v : ∀v:ι,   mul Zero v ≡ Zero = {}
val add_zero_n : ∀n∈nat, add Zero n ≡ n    = fun _ { {} }
val mul_zero_n : ∀n∈nat, mul Zero n ≡ Zero = fun _ { {} }

val rec add_n_zero : ∀n∈nat, add n Zero ≡ n =
  fun n {
    case n {
      Zero    → {}
      Succ[k] → let ih = add_n_zero k; {}
    }
  }

val rec add_succ : ∀n m∈nat, add n Succ[m] ≡ Succ[add n m] =
  fun n m {
    case n {
      Zero    → {}
      Succ[k] → let ih = add_succ k m; {}
    }
  }

val rec add_comm : ∀n m∈nat, add n m ≡ add m n =
  fun n m {
    case n {
      Zero    → let lem = add_n_zero m; {}
      Succ[k] → let ih = add_comm k m;
                let lem = add_succ m k; {}
    }
  }

val rec add_asso : ∀n m p∈nat, add n (add m p) ≡ add (add n m) p =
  fun n m p {
    case n {
      Zero    → {}
      Succ[k] → let ih = add_asso k m p; {}
    }
  }

val rec mul_n_zero : ∀n∈nat, mul n Zero ≡ Zero =
  fun n {
    case n {
      Zero    → {}
      Succ[k] → let ih = mul_n_zero k; {}
    }
  }

val rec mul_succ : ∀n m∈nat, mul n Succ[m] ≡ add (mul n m) n =
  fun n m {
    case n {
      Zero    → {}
      Succ[k] → set auto 0 3;
                let lem = mul_succ k m;
                let lem = add_succ (add m (mul k m)) k;
                let lem = add_asso m (mul k m) k;
                {}
    }
  }

val rec mul_comm : ∀n m∈nat, mul n m ≡ mul m n =
  fun n m {
    case n {
      Zero    → let lem = mul_n_zero m; {}
      Succ[k] → let ih  = mul_comm m k;
                let lem = mul_succ m k;
                let lem = add_comm (mul k m) m; {}
    }
  }

val rec mul_comm : ∀n m∈nat, mul n m ≡ mul m n =
  fun n m {
    case n {
      Zero    → let ded : mul Zero m ≡ Zero = {};
                let lem : mul m Zero ≡ Zero = mul_n_zero m; {}
      Succ[k] → let ded : mul Succ[k] m ≡ add m (mul k m) = {};
                let ih  : mul k m ≡ mul m k = mul_comm m k;
                let lem : mul m Succ[k] ≡ add (mul m k) m =
                  mul_succ m k
               ;
                let lem : add (mul k m) m ≡ add m (mul k m) =
                  add_comm (mul k m) m
               ; {}
    }
  }

def t_deduce⟨f:ο⟩ : τ = ({} : f)
def t_show⟨f:ο, p:τ⟩ : τ = (p : f)

val rec mul_comm : ∀n m∈nat, mul n m ≡ mul m n =
  fun n m {
    case n {
      Zero    → t_deduce⟨mul Zero m ≡ Zero⟩;
                t_show⟨mul m Zero ≡ Zero, mul_n_zero m⟩
      Succ[k] → t_deduce⟨mul Succ[k] m ≡ add m (mul k m)⟩;
                t_show⟨mul k m ≡ mul m k, mul_comm k m⟩;
                t_show⟨mul m Succ[k] ≡ add (mul m k) m, mul_succ m k⟩;
                t_show⟨add (mul k m) m ≡ add m (mul k m), add_comm (mul k m) m⟩
    }
  }

include lib.bool

val t1 : ∀a∈bool, imp a a ≡ true = fun a {
    if a {showing a ≡ true; qed } else { qed }
   }