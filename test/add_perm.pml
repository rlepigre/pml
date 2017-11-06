
include lib.nat

val rec add_perm : nat ⇒ nat ⇒ nat =
  fun n m {
    case n { Zero → m | S[p] → S[add_perm m p] }
  }

val rec add_perm_total : ∀n m∈nat, ∃v:ι, add_perm n m ≡ v =
  fun n m {
    case n { Zero → {} | S[p] → add_perm_total m p }
  }

val rec add_perm_Zn : ∀n∈nat, add_perm Zero n ≡ n = fun n { {} }

val rec add_perm_nZ : ∀n∈nat, add_perm n Zero ≡ n =
  fun n { case n { Zero → {} | S[p] → {} } }

val rec add_perm_comm : ∀n m∈nat, add_perm n m ≡ add_perm m n =
  fun n m {
    case n {
      Zero  → add_perm_nZ m
      S[n'] →
        case m {
          Zero → add_perm_nZ n'
          S[m'] → add_perm_comm n' m'
        }
    }
  }

val rec add_perm_assoc : ∀n m p∈nat,
    add_perm n (add_perm m p) ≡ add_perm (add_perm n m) p =
  fun n m p {
    add_perm_total m p;
    case n {
    | Zero  → add_perm_nZ m ; add_perm_nZ (add_perm m p)
    | S[n'] →
      show add_perm (add_perm m p) n' ≡ add_perm n' (add_perm m p)
        using add_perm_comm (add_perm m p) n';
      show add_perm m n' ≡ add_perm n' m
        using add_perm_comm m n';
      add_perm_total n' m;
      show add_perm (add_perm n' m) p ≡ add_perm p (add_perm n' m)
        using add_perm_comm (add_perm n' m) p;
      add_perm_assoc n' m p
    }
  }

val rec add_perm_add : ∀n m∈nat, add_perm n m = add n m =
  fun n m {
    case n {
      Zero → {}
      S[k] → add_perm_comm m k; add_perm_add k m
    }
  }
