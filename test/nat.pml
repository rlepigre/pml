def nat : ο = μx [ Z of {} ∈ {} ; S of x ]

val zero : nat = Z[]
val succ : nat ⇒ nat = fun n → S[n]
val one  : nat = succ zero
val two  : nat = succ one

val id_nat : nat ⇒ nat = fix fun id_nat n →
  case n of
  | Z[] → Z[{}]
  | S[p] → succ (id_nat p)

val test : nat = id_nat two

val id_nat_id : ∀n∈nat, id_nat n ≡ n = fix fun id_nat_id m →
  case m of
  | Z[] → {}
  | S[p] → let lem = id_nat_id p in {}

val add : nat ⇒ nat ⇒ nat = fix fun add n m →
  case n of
  | Z[] → m
  | S[p] → succ (add p m)

val add_total :  ∀n m∈nat, ∃v:ι, add n m ≡ v = fix fun add_total n m →
  case n of
  | Z[] → {}
  | S[p] → let ind_hyp = add_total p m in {}

//val add_zero : ∀n∈nat, add n zero ≡ n = fix fun add_zero n →
//  case n of
//  | Z[] → {}
//  | S[p] → let ind_hyp : add p zero ≡ p = add_zero p in {}

val add_zero : ∀n∈nat, add n zero ≡ n = fix fun add_zero n →
  case n of
  | Z[] → {}
  | S[p] → let ind_hyp = add_zero p in {}

val add_succ : ∀n m∈nat, add n S[m] ≡ succ (add n m) = fix fun add_succ n m →
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
    let lem = add_succ n p in {}

//val add_asso : ∀n m q∈nat, add n (add m q) ≡ add (add n m) q =
//  fix fun add_asso n m q →
//    case n of
//    | Z[] → {}
//    | S[p] →
//      let tot1 = add_total m q in
//      let deduce : add n (add m q) ≡ succ (add p (add m q)) = {} in
//      let tot2 = add_total p m in
//      let deduce : add (add n m) q ≡ succ (add (add p m) q) = {} in
//      let ind_hyp = add_asso p m q in
//      let deduce : add (add p m) q ≡ add (add p m) q = {} in
//      ✂
