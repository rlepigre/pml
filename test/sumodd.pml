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
    Zero → qed
    S[p] → showing sum_odd p + u1 + u2 * p ≡ (u1 + p) ** u2;
           show sum_odd p ≡ p ** u2 using theorem p;
           let x = Var[u0];
           let env : nat ⇒ nat = fun v { p };
           use eval_cor semi_nat (x **_pn u2 +_pn pn.one +_pn (pn.cst u2) *_pn x) env;
           use eval_cor semi_nat ((pn.one +_pn x) **_pn u2) env;
           qed
  }
}