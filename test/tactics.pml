type rec nat = [ Zero ; Succ of nat ]

val rec add : nat ⇒ nat ⇒ nat = fun n m →
  case n {
    | Zero[_] → m
    | Succ[k] → Succ[add k m]
  }

val rec mul : nat ⇒ nat ⇒ nat = fun n m →
  case n {
    | Zero[_] → Zero
    | Succ[k] → add m (mul k m)
  }

val add_zero_v : ∀v↓, add Zero v ≡ v    = {}

val mul_zero_v : ∀v↓, mul Zero v ≡ Zero = {}

val add_zero_n : ∀n∈nat, add Zero n ≡ n    = fun _ → {}

val mul_zero_n : ∀n∈nat, mul Zero n ≡ Zero = fun _ → {}

val rec add_n_zero : ∀n∈nat, add n Zero ≡ n = fun n →
  case n {
    | Zero[_] → {}
    | Succ[k] → let ih = add_n_zero k in {}
  }

val rec add_succ : ∀n m∈nat, add n Succ[m] ≡ Succ[add n m] = fun n m →
  case n {
    | Zero[_] → {}
    | Succ[k] → let ih = add_succ k m in {}
  }

val rec add_comm : ∀n m∈nat, add n m ≡ add m n = fun n m →
  case n {
    | Zero[_] → let lem = add_n_zero m in {}
    | Succ[k] → let ih = add_comm k m in
                let lem = add_succ m k in {}
  }

val rec add_total : ∀n m∈nat, ∃v↓, add n m ≡ v = fun n m →
  case n {
    | Zero[_] → {}
    | Succ[k] → let ih = add_total k m in {}
  }

val rec add_asso : ∀n m p∈nat, add n (add m p) ≡ add (add n m) p =
  fun n m p →
    let tot_m_p = add_total m p in
    case n {
      | Zero[_] → {}
      | Succ[k] → let tot_k_m = add_total k m in
                  let ih = add_asso k m p in {}
    }

val rec mul_n_zero : ∀n∈nat, mul n Zero ≡ Zero = fun n →
  case n {
    | Zero[_] → {}
    | Succ[k] → let ih = mul_n_zero k in {}
  }

val rec mul_total : ∀n m∈nat, ∃v↓, mul n m ≡ v = fun n m →
  case n {
    | Zero[_] → {}
    | Succ[k] → let ih = mul_total k m in
                let lem = add_total m (mul k m) in {}
  }

val rec mul_succ : ∀n m∈nat, mul n Succ[m] ≡ add (mul n m) n = fun n m →
  case n {
    | Zero[_] → {}
    | Succ[k] → let lem = mul_succ k m in
                let tot = mul_total k m in
                let tot = add_total m (mul k m) in
                let lem = add_succ (add m (mul k m)) k in
                let lem = add_asso m (mul k m) k in
                let tot = mul_total k Succ[m] in {}
  }

val rec mul_comm : ∀n m∈nat, mul n m ≡ mul m n = fun n m →
  case n {
    | Zero[_] → let lem = mul_n_zero m in {}
    | Succ[k] → let ih  = mul_comm m k in
                let lem = mul_succ m k in
                let tot = mul_total k m in
                let lem = add_comm (mul k m) m in {}
  }

val rec mul_comm : ∀n m∈nat, mul n m ≡ mul m n = fun n m →
  case n {
    | Zero[_] → let ded : mul Zero m ≡ Zero = {} in
                let lem : mul m Zero ≡ Zero = mul_n_zero m in {}
    | Succ[k] → let ded : mul Succ[k] m ≡ add m (mul k m) = {} in
                let ih  : mul k m ≡ mul m k = mul_comm m k in
                let lem : mul m Succ[k] ≡ add (mul m k) m =
                  mul_succ m k
                in
                let tot : (∃v:ι, mul k m ≡ v) = mul_total k m in
                let lem : add (mul k m) m ≡ add m (mul k m) =
                  add_comm (mul k m) m
                in {}
  }

def t_deduce<f:ο> : τ = ({} : f)
def t_show<f:ο, p:τ> : τ = (p : f)

val rec mul_comm : ∀n m∈nat, mul n m ≡ mul m n = fun n m →
  case n {
    | Zero[_] → t_deduce<mul Zero m ≡ Zero>;
                t_show<mul m Zero ≡ Zero, mul_n_zero m>
    | Succ[k] → t_deduce<mul Succ[k] m ≡ add m (mul k m)>;
                t_show<mul k m ≡ mul m k, mul_comm k m>;
                t_show<mul m Succ[k] ≡ add (mul m k) m, mul_succ m k>;
                t_show<(∃v:ι, mul k m ≡ v), mul_total k m>;
                t_show<add (mul k m) m ≡ add m (mul k m), add_comm (mul k m) m>
  }