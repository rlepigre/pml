include lib.nat
include test.polynomials

val rec sum_odd : nat ⇒ nat = fun n {
  case n {
    Zero → 0
    S[p] → sum_odd p + 1 + 2 * p
  }
}

val rec theorem : ∀n∈nat, sum_odd n ≡ n ** 2 = fun n {
  case n {
    Zero → eqns sum_odd 0 ≡ 0 ≡ 0 ** 2
    S[p] → eqns
           sum_odd n ≡ sum_odd p + 1 + 2 * p
                     ≡ p ** 2 + 1 + 2 * p    by theorem p
                     ≡ (1 + p) ** 2           using {
                       let simpl = simpl1 semi_nat p;
                       use simpl (fun p { p **_pn 2 +_pn pn.one +_pn (pn.cst 2) *_pn p});
                       use simpl (fun p { (pn.one +_pn p) **_pn 2})
                     }
                     ≡ n ** 2
  }
}
