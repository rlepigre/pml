include lib.nat
include test.polynomials

val rec sum_odd : nat ⇒ nat = fun n {
  case n {
    Zero → u0
    S[p] → sum_odd p + u1 + u2 * p
  }
}


val rec theorem : ∀n∈nat, sum_odd n ≡ n ** u2 = fun n {
  case n {
    Zero → eqns sum_odd u0 ≡ u0 ≡ u0 ** u2
    S[p] → eqns
           sum_odd n ≡ sum_odd p + u1 + u2 * p
                     ≡ p ** u2 + u1 + u2 * p    by theorem p
                     ≡ (u1 + p) ** u2           using {
                       let simpl = simpl1 semi_nat p;
                       use simpl (fun x { x **_pn u2 +_pn pn.one +_pn (pn.cst u2) *_pn x});
                       use simpl (fun x { (pn.one +_pn x) **_pn u2})
                     }
                     ≡ n ** u2
  }
}
