type rec nat = [ Z ; S of nat ]

val zero : nat = Z
val succ : nat ⇒ nat = fun n { S[n] }
val one  : nat = succ zero
val two  : nat = succ one

val rec id_nat : nat ⇒ nat =
  fun n {
    case n {
      | Z    → zero
      | S[p] → succ (id_nat p)
    }
  }

val test : nat = id_nat two

val rec id_nat_id : ∀n∈nat, id_nat n ≡ n =
  fun m {
    case m {
      | Z    → {}
      | S[p] → let ind_hyp : id_nat p ≡ p = id_nat_id p; {}
    }
  }

val rec add : nat ⇒ nat ⇒ nat =
  fun n m {
    case n {
      Z    → m
      S[p] → succ (add p m)
    }
  }

val partial_add_total : ∀x:ι, ∃v:ι, add x ≡ v = {}

val rec strong_add_total : ∀n∈nat, ∀m∈(∃x,x), ∃v:ι, add n m ≡ v =
  fun n m {
    case n {
      Z    → {}
      S[p] → use strong_add_total p m
    }
  }

val rec add_total : ∀n m∈nat, ∃v:ι, add n m ≡ v =
  fun n m {
    case n {
      Z    → {}
      S[p] → let ind_hyp = add_total p m; {}
    }
  }

def addt<x:τ,y:τ> : τ =
   let lem = add_total x y; add x y

val add_zero_left : ∀z∈nat, add zero z ≡ z = λn.{}

val rec add_zero1 : ∀z∈nat, add z zero ≡ z =
  fun k {
    case k {
      | Z    → {}
      | S[p] → let ind_hyp = (add_zero1 p : add p zero ≡ p); {}
    }
  }

val rec add_zero2 : ∀n∈nat, add n zero ≡ n =
  fun n {
    case n {
      Z    → {}
      S[p] → let ind_hyp : add p zero ≡ p = add_zero2 p; {}
    }
  }

val rec add_asso : ∀n m q∈nat, add n (add m q) ≡ add (add n m) q =
  fun n m q {
    let tot1 = add_total m q;
    case n {
      Z    → {}
      S[p] →
        let ded : add n (add m q) ≡ succ (add p (add m q)) = {};
        let tot2 = add_total p m;
        let ded : add (add n m) q ≡ succ (add (add p m) q) = {};
        let ind_hyp = add_asso p m q; {}
    }
  }

val rec add_zero : ∀n∈nat, add n zero ≡ n =
  fun n {
    case n {
      Z    → {}
      S[p] → add_zero p
    }
  }

val rec add_succ : ∀n m∈nat, add n S[m] ≡ succ(add n m) =
  fun n m {
    case n {
      Z    → {}
      S[p] → let ind_hyp = add_succ p m; {}
    }
  }

val rec add_succ2 : ∀n m∈nat, add n S[m] ≡ S[add n m] =
  fun n m {
    case n {
      Z    → {}
      S[p] → let ind_hyp : add p S[m] ≡ S[add p m] = add_succ p m; {}
    }
  }

val rec add_comm : ∀n m∈nat, add n m ≡ add m n =
  fun n m {
    case n {
      Z    → let lem = add_zero m; {}
      S[p] → let ind_hyp = add_comm p m;
             let lem = add_succ m p; {}
    }
  }

val rec mul : nat ⇒ nat ⇒ nat =
  fun n m {
    case n {
      Z    → Z
      S[p] → add m (mul p m)
    }
  }

val rec mul_total : ∀n m∈nat, ∃v:ι, mul n m ≡ v =
  fun n m {
    case n {
      Z    → {}
      S[p] → let ind_hyp = mul_total p m;
             let lem = add_total m (mul p m); {}
    }
  }

val rec mul_zero : ∀n∈nat, mul n zero ≡ zero =
  fun n {
    case n {
      Z    → {}
      S[p] → let ind_hyp : mul p zero ≡ zero = mul_zero p;
             let ded : add zero (mul p zero) ≡ mul n zero = {};
             let ded : add zero (mul p zero) ≡ zero = {}; {}
    }
  }

val rec mul_zero1 : ∀n∈nat, mul n zero ≡ zero =
  fun n {
    case n {
      Z    → {}
      S[p] → mul_zero p
    }
  }

val rec mul_succ : ∀n m∈nat, mul n S[m] ≡ add (mul n m) n =
  fun n m {
    case n {
      Z    → {}
      S[p] →
        let ded : add (mul n m) n ≡ add (add m (mul p m)) n = {};
        let ind_hyp : mul p S[m] ≡ add (mul p m) p = mul_succ p m;
        let total = mul_total p m;
        let total = add_total m (mul p m);
        let ded : add (add m (mul p m)) n ≡ succ (add (add m (mul p m)) p) =
          add_succ (add m (mul p m)) p;
        let ded : add (add m (mul p m)) n ≡ succ (add m (add (mul p m) p)) =
          add_asso m (mul p m) p;
        let ded : add (add m (mul p m)) n ≡ succ (add m (mul p S[m])) =
          {};
        let total = mul_total p S[m];
        let ded : add (add m (mul p m)) n ≡ add S[m] (mul p S[m]) = {};
        let ded : add (add m (mul p m)) n ≡ mul n S[m] = {}; {}
    }
  }

val rec mul_comm : ∀n m∈nat, mul n m ≡ mul m n =
  fun n m {
    case n {
      Z    → let lem = mul_zero m; {}
      S[p] → let ind : mul p m ≡ mul m p = mul_comm m p;
             let lem = mul_succ m p;
             let tot = mul_total p m;
             let lem = add_comm (mul p m) m; {}
    }
  }

def add_all3<a:τ,b:τ,c:τ> =
  let lem = add_total a b;
  let lem = add_total a c;
  let lem = add_total b c;
  let lem = add_comm a b;
  let lem = add_comm a c;
  let lem = add_comm b c;
  let lem = add_asso a b c;
  let lem = add_asso a c b;
  {}

def add_all4<a:τ,b:τ,c:τ,d:τ> =
  let lem = add_all3<a,b,c>;
  let lem = add_all3<a,b,d>;
  let lem = add_all3<a,c,d>;
  let lem = add_all3<b,c,d>;
  {}

val rec mul_dist_l : ∀p n m∈nat, mul p (add n m) ≡ add (mul p n) (mul p m) =
  fun p n m {
    case p {
      Z     → let lem = add_total n m; {}
      S[p'] →
        let lem = add_total n m;
        let ded : mul p (add n m) ≡ add (add n m) (mul p' (add n m)) = {};
        let ded : add (mul p n) (mul p m) ≡
                     add (add n (mul p' n)) (add m (mul p' m)) = {};
        let ind : mul p' (add n m) ≡ add (mul p' n) (mul p' m) =
           mul_dist_l p' n m;
        let lem = mul_total p' n;
        let lem = mul_total p' m;
        let lem = add_all4<n, (mul p' n), m, (mul p' m)>;
        let lem = add_total m (mul p' m);
        let lem : add (add n (mul p' n)) (add m (mul p' m)) ≡
                  add n (add (mul p' n) (add m (mul p' m))) =
                add_asso n (mul p' n) (add m (mul p' m));
        let lem : add (add n (mul p' n)) (add m (mul p' m)) ≡
                  add n (add (add (mul p' n) m) (mul p' m)) =
                add_asso (mul p' n) m (mul p' m);
        let lem : add (add n (mul p' n)) (add m (mul p' m)) ≡
                  add n (add (add m (mul p' n)) (mul p' m)) =
                add_comm m (mul p' n);
        let lem : add (add n (mul p' n)) (add m (mul p' m)) ≡
                  add n (add m (add (mul p' n) (mul p' m))) =
                add_asso m (mul p' n) (mul p' m);
        let lem = add_total (mul p' n) (mul p' m);
        let lem : add (add n (mul p' n)) (add m (mul p' m)) ≡
                  add (add n m) (add (mul p' n) (mul p' m)) =
                add_asso n m (add (mul p' n) (mul p' m));
        {}
    }
  }

val mul_dist_r : ∀n m p∈nat, mul (add n m) p ≡ add (mul n p) (mul m p) =
  fun n m p {
    let lem = add_total n m;
    let lem = mul_comm (add n m) p;
    let lem = mul_comm n p;
    let lem = mul_comm m p;
    let lem = mul_dist_l p n m;
    {}
  }

val rec mul_asso : ∀n m p∈nat, mul (mul n m) p ≡ mul n (mul m p) =
  fun n m p {
    case n {
      Z     → let lem = mul_total m p; {}
      S[n'] →
        let ded : mul (mul n m) p ≡ mul (add m (mul n' m)) p = {};
        let lem = mul_total m p;
        let ded : mul n (mul m p) ≡ add (mul m p) (mul n' (mul m p)) = {};
        let lem = mul_total n' m;
        let lem : mul (mul n m) p ≡ add (mul m p) (mul (mul n' m) p) =
          mul_dist_r m (mul n' m) p;
        let lem : mul (mul n m) p ≡ add (mul m p) (mul n' (mul m p)) =
          mul_asso n' m p;
        {}
    }
  }

// Proof by induction.
val rec ind : ∀f:ι→ο, f<Z> ⇒ (∀i∈nat, f<i> ⇒ f<S[i]>) ⇒ ∀n∈nat, f<n> =
  fun d s n {
    case n {
      Z[_] → d
      S[k] → s k (ind d s k)
    }
  }

// Proof by induction.
def ind2<f:ι→ο,z:τ,s:τ> : τ = (ind z s : ∀n∈nat, f<n>)

def p<n:ι> : ο =  id_nat n ≡ n

//val rec id_nat_id : ∀n∈nat, id_nat n ≡ n = ind2<p,{},(fun i x → x)>
