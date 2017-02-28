def nat : ο = μx [ Z of {} ∈ {} ; S of x ]

val zero : nat = Z[]
val succ : nat ⇒ nat = fun n → S[n]
val one  : nat = succ zero
val two  : nat = succ one

val id_nat : nat ⇒ nat = fix fun id_nat n →
  case n of
  | Z[] → Z[]
  | S[p] → succ (id_nat p)

val test : nat = id_nat two

val id_nat_id : ∀n∈nat, id_nat n ≡ n = fix fun id_nat_id m →
  case m of
  | Z[] → {}
  | S[p] → let ind_hyp : id_nat p ≡ p = id_nat_id p in {}

val add : nat ⇒ nat ⇒ nat = fix fun add n m →
  case n of
  | Z[] → m
  | S[p] → succ (add p m)

val add_total : ∀n m∈nat, ∃v:ι, add n m ≡ v = fix fun add_total n m →
  case n of
  | Z[] → {}
  | S[p] → let ind_hyp = add_total p m in {}

val add_zero_left : ∀z∈nat, add zero z ≡ z = fun n → {}

val add_zero1 : ∀z∈nat, add z zero ≡ z = fix fun add_zero k →
  case k of
  | Z[] → {}
  | S[p] →
    let ind_hyp = (add_zero p : add p zero ≡ p) in {}

val add_zero2 : ∀n∈nat, add n zero ≡ n = fix fun add_zero n →
  case n of
  | Z[] → {}
  | S[p] → let ind_hyp : add p zero ≡ p = add_zero p in {}

val add_asso : ∀n m q∈nat, add n (add m q) ≡ add (add n m) q =
  fix fun add_asso n m q →
    let tot1 = add_total m q in
    case n of
    | Z[] → {}
    | S[p] →
      let deduce : add n (add m q) ≡ succ (add p (add m q)) = {} in
      let tot2 = add_total p m in
      let deduce : add (add n m) q ≡ succ (add (add p m) q) = {} in
      let ind_hyp = add_asso p m q in
      let deduce : add (add p m) q ≡ add (add p m) q = {} in
      {}

val add_zero : ∀n∈nat, add n zero ≡ n = fix fun add_zero n →
  case n of
  | Z[] → {}
  | S[p] → let ind_hyp = add_zero p in {}

val add_succ : ∀n m∈nat, add n S[m] ≡ succ(add n m) = fix fun add_succ n m →
  case n of
  | Z[] → {}
  | S[p] → let ind_hyp = add_succ p m in {}

//val add_succ : ∀n m∈nat, add n S[m] ≡ succ (add n m) = fix fun add_succ n m →
//  case n of
//  | Z[] → {}
//  | S[p] → let ind_hyp = add_succ p m in {}

//val add_succ : ∀n m∈nat, add n S[m] ≡ S[add n m] = fix fun add_succ n m →
//  case n of
//  | Z[] → {}
//  | S[p] → let ind_hyp : add p S[m] ≡ S[add p m] = add_succ p m in {}

val add_comm : ∀n m∈nat, add n m ≡ add m n = fix fun add_comm n m →
  case n of
  | Z[] → let lem = add_zero m in {}
  | S[p] →
    let ind_hyp = add_comm p m in
    let lem = add_succ m p in
    {}

val mul : nat ⇒ nat ⇒ nat = fix fun mul n m →
  case n of
  | Z[] → Z[]
  | S[p] → add m (mul p m)

val mul_total : ∀n m∈nat, ∃v:ι, mul n m ≡ v = fix fun mul_total n m →
  case n of
  | Z[] → {}
  | S[p] →
   let ind_hyp = mul_total p m in
   let lem = add_total m (mul p m) in
   {}

val mul_zero : ∀n∈nat, mul n zero ≡ zero = fix fun mul_zero n →
  case n of
  | Z[] → {}
  | S[p] →
    let ind_hyp : mul p zero ≡ zero = mul_zero p in
    let deduce : add zero (mul p zero) ≡ mul n zero = {} in
    let deduce : add zero (mul p zero) ≡ zero = {} in
    {}
val mul_zero1 : ∀n∈nat, mul n zero ≡ zero = fix fun mul_zero n →
  case n of
  | Z[]  → {}
  | S[p] → let ind_hyp = mul_zero p in {}

val mul_succ : ∀n m∈nat, mul n S[m] ≡ add (mul n m) n = fix fun mul_succ n m →
  case n of
  | Z[]  → {}
  | S[p] →
    let deduce : add (mul n m) n ≡ add (add m (mul p m)) n = {} in
    let ind_hyp : mul p S[m] ≡ add (mul p m) p = mul_succ p m in
    let total = mul_total p m in
    let total = add_total m (mul p m) in
    let deduce : add (add m (mul p m)) n ≡ succ (add (add m (mul p m)) p) =
      add_succ (add m (mul p m)) p
    in
    let deduce : add (add m (mul p m)) n ≡ succ (add m (add (mul p m) p)) =
      add_asso m (mul p m) p
    in
    let deduce : add (add m (mul p m)) n ≡ succ (add m (mul p S[m])) =
      {}
    in
    let total = mul_total p S[m] in
    let deduce : add (add m (mul p m)) n ≡ add S[m] (mul p S[m]) =
      {}
    in
    let deduce : add (add m (mul p m)) n ≡ mul n S[m] =
      {}
    in
    {}

val mul_comm : ∀n m∈nat, mul n m ≡ mul m n = fix fun mul_comm n m →
  case n of
  | Z[]  → let lem = mul_zero m in {}
  | S[p] →
     let ind : mul p m ≡ mul m p = mul_comm m p in
     let lem = mul_succ m p in
     let tot = mul_total p m in
     let lem = add_comm (mul p m) m in
     {}

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
    case p of
    | Z[] →
       let lem = add_total n m in {}
    | S[p'] →
       let lem = add_total n m in
       let deduce : mul p (add n m) ≡ add (add n m) (mul p' (add n m)) = {} in
       let deduce : add (mul p n) (mul p m) ≡
                    add (add n (mul p' n)) (add m (mul p' m)) = {} in
       let ind : mul p' (add n m) ≡ add (mul p' n) (mul p' m) =
          mul_dist p' n m
       in
       let lem = mul_total p' n in
       let lem = mul_total p' m in
       // let lem = add_all4<n, (mul p' n), m, (mul p' m)> in FIXME loops
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
    case n of
    | Z[] →
       let lem = mul_total m p in {}
    | S[n'] →
       let deduce : mul (mul n m) p ≡ mul (add m (mul n' m)) p = {} in
       let lem = mul_total m p in
       let deduce : mul n (mul m p) ≡ add (mul m p) (mul n' (mul m p)) = {} in
       let lem = mul_total n' m in
       let lem : mul (mul n m) p ≡ add (mul m p) (mul (mul n' m) p) =
         mul_dist_r m (mul n' m) p in
       let lem : mul (mul n m) p ≡ add (mul m p) (mul n' (mul m p)) =
         mul_asso n' m p in
       {}