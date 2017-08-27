type rec list<a> = [Nil ; Cons of {hd : a ; tl : list}]

val rec exists : ∀a, (a ⇒ bool) ⇒ list<a> ⇒ bool =
  fun pred l {
    case l {
      Nil[_]  → false
      Cons[c] → if pred c.hd then true else exists pred c.tl
    }
  }

val rec fold_left : ∀a b, (a ⇒ b ⇒ a) ⇒ a ⇒ list<b> ⇒ a =
  fun f acc l {
    case l {
      Nil     → acc
      Cons[c] → fold_left f (f acc c.hd) c.tl
    }
  }
val exists : ∀a, (a ⇒ bool) ⇒ list<a> ⇒ bool =
  fun pred l {
    let f = fun acc e { if pred e { true } else { acc } } in
    fold_left f false l
  }
include lib.option
val silly : (∀a, a ⇒ a) ⇒ {} ⇒ option<{}> =
  fun f u { f Some[f u] }
val exists : ∀a, (a ⇒ bool) ⇒ list<a> ⇒ bool =
  fun pred l {
    save k {
      case l {
        Nil[_]  → true
        Cons[c] → if c.hd then conjunction c.tl else restore k false
      }
    }
  }
val peirce : ∀a b, ((a ⇒ b) ⇒ a) ⇒ a =
  fun x {
    save k { x (fun y { restore k y }) }
  }

// Usual definition of logical negation
type neg<a> = a ⇒ ∀x, x

val dneg_elim : ∀a, neg<neg<a>> ⇒ a =
  peirce

// Disjoint sum of two types (logical disjunction)
type either<a,b> = [InL of a ; InR of b]

val excl_mid : ∀a, {} ⇒ either<a, neg<a>> =
  fun _ {
    save k { InR[fun x → restore k InL[x]] }
  }
type rec nat = [Zero ; Succ of nat]

val rec add : nat ⇒ nat ⇒ nat =
  fun n m {
    case n {
      Zero    → m
      Succ[k] → Succ[add k m]
    }
  }
val add_z_n : ∀n:ι, add Zero n ≡ n = {}
// val add_n_z : ∀n:ι, add n Zero ≡ n = {}
val rec add_n_z : ∀n∈nat, add n Zero ≡ n =
  fun n {
    case n {
      Zero    → {}
      Succ[k] → let ih = add_n_z k; {}
    }
  }
// val rec add_n_z_loop : ∀n∈nat, add n Zero ≡ n =
//   fun n { let ih = add_n_z_loop n in {} }
val rec add_n_s : ∀n m∈nat, add n Succ[m] ≡ Succ[add n m] =
  fun n m {
    case n {
      Zero    → {}
      Succ[k] → let ind_hyp = add_n_s k m; {}
    }
  }
val rec add_comm : ∀n m∈nat, add n m ≡ add m n =
  fun n m {
    case n {
      Zero    → let lem = add_n_z m in {}
      Succ[k] → let ih  = add_comm k m in
                let lem = add_n_s m k in {}
    }
  }
val rec add_total : ∀n m∈nat, ∃v:ι, add n m ≡ v =
  fun n m {
    case n {
      Zero    → {}
      Succ[k] → let ih = add_total k m; {}
    }
  }
val rec add_asso : ∀n m p∈nat, add n (add m p) ≡ add (add n m) p =
  fun n m p {
    let tot_m_q = add_total m p in
    case n {
      Zero[_] → {}
      Succ[k] → let tot_p_m = add_total k m in
                let ih = add_asso k m p in {}
    }
  }
