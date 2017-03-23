type rec nat = [ Z ; S of nat ]

val zero : nat = Z[]
val succ : nat ⇒ nat = fun n → S[n]
val one  : nat = succ zero
val two  : nat = succ one

val rec id_nat : nat ⇒ nat = fun n →
  case n {
    | Z[] → Z[]
    | S[p] → succ (id_nat p)
  }

val test : nat = id_nat two

val rec id_nat_id : ∀n∈nat, id_nat n ≡ n = fun m →
  case m {
    | Z[] → {}
    | S[p] → let ind_hyp : id_nat p ≡ p = id_nat_id p in {}
  }

val rec add : nat ⇒ nat ⇒ nat = fun n m →
  case n {
    | Z[] → m
    | S[p] → succ (add p m)
  }

val partial_add_total : ∀x↓, ∃v↓, add x ≡ v = {}

val rec strong_add_total : ∀n∈nat, ∀m∈(∃x,x), ∃v↓, add n m ≡ v = fun n m →
  case n {
    | Z[_] → {}
    | S[p] → let ind_hyp = strong_add_total p m in {}
  }

// FIXME should work
//val rec strong_add_total2 : ∀m↓, ∀n∈nat, ∃v↓, add n m ≡ v =  Λm:ι. fun n →
//  case n {
//    | Z[_] → {}
//    | S[p] → let ded  : add n m ≡ S[add p m] = {} in
//             let ind_hyp : (∃v↓, add p m ≡ v) = strong_add_total2 p in ✂
//  }

val rec add_total : ∀n m∈nat, ∃v↓, add n m ≡ v = fun n m →
  case n {
    | Z[] → {}
    | S[p] → let ind_hyp = add_total p m in {}
  }

def addt<x:τ,y:τ> : τ =
   let lem = add_total x y in add x y

val add_zero_left : ∀z∈nat, add zero z ≡ z = fun n → {}

val rec add_zero1 : ∀z∈nat, add z zero ≡ z = fun k →
  case k {
    | Z[] → {}
    | S[p] → let ind_hyp = (add_zero1 p : add p zero ≡ p) in {}
  }

val rec add_zero2 : ∀n∈nat, add n zero ≡ n = fun n →
  case n {
    | Z[] → {}
    | S[p] → let ind_hyp : add p zero ≡ p = add_zero2 p in {}
  }

val rec add_asso : ∀n m q∈nat, add n (add m q) ≡ add (add n m) q =
  fun n m q →
    let tot1 = add_total m q in
    case n {
      | Z[] → {}
      | S[p] →
         let ded : add n (add m q) ≡ succ (add p (add m q)) = {} in
         let tot2 = add_total p m in
         let ded : add (add n m) q ≡ succ (add (add p m) q) = {} in
         let ind_hyp = add_asso p m q in {}
    }

val rec add_zero : ∀n∈nat, add n zero ≡ n = fun n →
  case n {
    | Z[] → {}
    | S[p] → let ind_hyp = add_zero p in {}
  }

val rec add_succ : ∀n m∈nat, add n S[m] ≡ succ(add n m) = fun n m →
  case n {
    | Z[] → {}
    | S[p] → let ind_hyp = add_succ p m in {}
  }

val rec add_succ2 : ∀n m∈nat, add n S[m] ≡ S[add n m] = fun n m →
  case n {
    | Z[] → {}
    | S[p] → let ind_hyp : add p S[m] ≡ S[add p m] = add_succ p m in {}
  }

val add_comm : ∀n m∈nat, add n m ≡ add m n = fix fun add_comm n m →
  case n {
    | Z[]  → let lem = add_zero m in {}
    | S[p] → let ind_hyp = add_comm p m in
             let lem = add_succ m p in {}
  }

val mul : nat ⇒ nat ⇒ nat = fix fun mul n m →
  case n {
    | Z[] → Z[]
    | S[p] → add m (mul p m)
  }

val mul_total : ∀n m∈nat, ∃v↓, mul n m ≡ v = fix fun mul_total n m →
  case n {
    | Z[]  → {}
    | S[p] → let ind_hyp = mul_total p m in
             let lem = add_total m (mul p m) in {}
  }

val mul_zero : ∀n∈nat, mul n zero ≡ zero = fix fun mul_zero n →
  case n {
    | Z[]  → {}
    | S[p] → let ind_hyp : mul p zero ≡ zero = mul_zero p in
             let ded : add zero (mul p zero) ≡ mul n zero = {} in
             let ded : add zero (mul p zero) ≡ zero = {} in {}
  }

val mul_zero1 : ∀n∈nat, mul n zero ≡ zero = fix fun mul_zero n →
  case n {
    | Z[]  → {}
    | S[p] → let ind_hyp = mul_zero p in {}
  }

val mul_succ : ∀n m∈nat, mul n S[m] ≡ add (mul n m) n = fix fun mul_succ n m →
  case n {
    | Z[]  → {}
    | S[p] →
       let ded : add (mul n m) n ≡ add (add m (mul p m)) n = {} in
       let ind_hyp : mul p S[m] ≡ add (mul p m) p = mul_succ p m in
       let total = mul_total p m in
       let total = add_total m (mul p m) in
       let ded : add (add m (mul p m)) n ≡ succ (add (add m (mul p m)) p) =
         add_succ (add m (mul p m)) p
       in
       let ded : add (add m (mul p m)) n ≡ succ (add m (add (mul p m) p)) =
         add_asso m (mul p m) p
       in
       let ded : add (add m (mul p m)) n ≡ succ (add m (mul p S[m])) =
         {}
       in
       let total = mul_total p S[m] in
       let ded : add (add m (mul p m)) n ≡ add S[m] (mul p S[m]) = {} in
       let ded : add (add m (mul p m)) n ≡ mul n S[m] = {} in {}
  }

val mul_comm : ∀n m∈nat, mul n m ≡ mul m n = fix fun mul_comm n m →
  case n {
    | Z[]  → let lem = mul_zero m in {}
    | S[p] → let ind : mul p m ≡ mul m p = mul_comm m p in
             let lem = mul_succ m p in
             let tot = mul_total p m in
             let lem = add_comm (mul p m) m in {}
  }

def add_all3<a:τ,b:τ,c:τ> =
  let lem = add_total a b in
  let lem = add_total a c in
  let lem = add_total b c in
  let lem = add_comm a b in
  let lem = add_comm a c in
  let lem = add_comm b c in
  let lem = add_asso a b c in
  let lem = add_asso a c b in
  {}

def add_all4<a:τ,b:τ,c:τ,d:τ> =
  let lem = add_all3<a,b,c> in
  let lem = add_all3<a,b,d> in
  let lem = add_all3<a,c,d> in
  let lem = add_all3<b,c,d> in
  {}

val mul_dist_l : ∀p n m∈nat, mul p (add n m) ≡ add (mul p n) (mul p m) =
  fix fun mul_dist p n m  →
    case p {
    | Z[] →
       let lem = add_total n m in {}
    | S[p'] →
       let lem = add_total n m in
       let ded : mul p (add n m) ≡ add (add n m) (mul p' (add n m)) = {} in
       let ded : add (mul p n) (mul p m) ≡
                    add (add n (mul p' n)) (add m (mul p' m)) = {} in
       let ind : mul p' (add n m) ≡ add (mul p' n) (mul p' m) =
          mul_dist p' n m
       in
       let lem = mul_total p' n in
       let lem = mul_total p' m in
       //let lem = add_all4<n, (mul p' n), m, (mul p' m)> in FIXME loops
       let lem = add_total m (mul p' m) in
       let lem : add (add n (mul p' n)) (add m (mul p' m)) ≡
                 add n (add (mul p' n) (add m (mul p' m))) =
               add_asso n (mul p' n) (add m (mul p' m))
       in
       let lem : add (add n (mul p' n)) (add m (mul p' m)) ≡
                 add n (add (add (mul p' n) m) (mul p' m)) =
               add_asso (mul p' n) m (mul p' m)
       in
       let lem : add (add n (mul p' n)) (add m (mul p' m)) ≡
                 add n (add (add m (mul p' n)) (mul p' m)) =
               add_comm m (mul p' n)
       in
       let lem : add (add n (mul p' n)) (add m (mul p' m)) ≡
                 add n (add m (add (mul p' n) (mul p' m))) =
               add_asso m (mul p' n) (mul p' m)
       in
       let lem = add_total (mul p' n) (mul p' m) in
       let lem : add (add n (mul p' n)) (add m (mul p' m)) ≡
                 add (add n m) (add (mul p' n) (mul p' m)) =
               add_asso n m (add (mul p' n) (mul p' m))
       in
       {}
    }

val mul_dist_r : ∀n m p∈nat, mul (add n m) p ≡ add (mul n p) (mul m p) =
  fun n m p →
    let lem = add_total n m in
    let lem = mul_comm (add n m) p in
    let lem = mul_comm n p in
    let lem = mul_comm m p in
    let lem = mul_dist_l p n m in
    {}

val mul_asso : ∀n m p∈nat, mul (mul n m) p ≡ mul n (mul m p) =
  fix fun mul_asso n m p →
    case n {
    | Z[] →
       let lem = mul_total m p in {}
    | S[n'] →
       let ded : mul (mul n m) p ≡ mul (add m (mul n' m)) p = {} in
       let lem = mul_total m p in
       let ded : mul n (mul m p) ≡ add (mul m p) (mul n' (mul m p)) = {} in
       let lem = mul_total n' m in
       let lem : mul (mul n m) p ≡ add (mul m p) (mul (mul n' m) p) =
         mul_dist_r m (mul n' m) p in
       let lem : mul (mul n m) p ≡ add (mul m p) (mul n' (mul m p)) =
         mul_asso n' m p in
       {}
    }

// Proof by induction.
val rec ind : ∀f:ι→ο, f<Z> ⇒ (∀i∈nat, f<i> ⇒ f<S[i]>) ⇒ ∀n∈nat, f<n> =
 fun d s n →
   case n {
     | Z[_] → d
     | S[k] → s k (ind d s k)
   }

// Proof by induction.
def ind2<f:ι→ο,z:τ,s:τ> : τ = (ind z s : ∀n∈nat, f<n>)

def p<n:ι> : ο =  id_nat n ≡ n

//val rec id_nat_id : ∀n∈nat, id_nat n ≡ n = ind2<p,{},(fun i x → x)>
