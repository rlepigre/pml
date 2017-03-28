type rec nat = [Z ; S of nat]

val zero : nat = Z[{}]
val succ : nat ⇒ nat = fun n → S[n]

val pred : [S of nat] ⇒ nat = fun n →
  case n { S[n] → n }

val rec add : nat ⇒ nat ⇒ nat = fun n m →
  case n {
    | Z[_] → m
    | S[k] → succ (add k m)
  }

val rec mul : nat ⇒ nat ⇒ nat = fun n m →
  case n {
    | Z[_] → zero
    | S[k] → add m (mul k m)
  }

// Examples
val one : nat = succ zero
val two : nat = succ (succ zero)
val six : nat = mul two (succ two)

val rec compare : nat ⇒ nat ⇒ [Ls ; Eq ; Gr] = fun n m →
  case n {
    | Z[_] → case m {
               | Z[_] → Eq
               | S[_] → Ls
             }
    | S[n] → case m {
               | Z[_] → Gr
               | S[m] → compare n m
             }
  }

val eq : nat ⇒ nat ⇒ bool = fun n m →
  case compare n m {
    | Ls[_] → false
    | Eq[_] → true
    | Gr[_] → false
  }

val rec add_total : ∀n m∈nat, ∃v:ι↓, add n m ≡ v = fun n m →
  case n {
    | Z[_] → qed
    | S[k] → use add_total k m; qed
  }

val rec add_assoc : ∀m n p∈nat, add m (add n p) ≡ add (add m n) p =
  fun m n p →
    use add_total n p;
    case m {
      | Z[_] → deduce add Z (add n p) ≡ add (add Z n) p;
               deduce add n p ≡ add (add Z n) p;
               deduce add n p ≡ add n p;
               qed
      | S[k] → show add k (add n p) ≡ add (add k n) p using add_assoc k n p;
               deduce S[add k (add n p)] ≡ S[add (add k n) p];
               deduce add S[k] (add n p) ≡ S[add (add k n) p];
               use add_total k n;
               deduce add S[k] (add n p) ≡ add S[add k n] p;
               deduce add S[k] (add n p) ≡ add (add S[k] n) p;
               qed
    }
