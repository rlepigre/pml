include lib.nat
include tests.polynomials

val test1 : poly⟨nat⟩ =
    let x = Var[0];
    let y = Var[1];
    tpoly_to_poly semi_nat ((x +~ y) **~ 2)

val test2 : poly⟨nat⟩ =
    let x = Var[0];
    let y = Var[1];
    tpoly_to_poly semi_nat ((x +~ y) *~ (x +~ y))

val test3 : test1 ≡ test2 = qed

val test4 : poly⟨nat⟩ =
    let x = Var[0];
    let y = Var[1];
    tpoly_to_poly semi_nat (x **~ 2 +~ Cst[2] *~ (x *~ y) +~ y **~ 2)

val test5 : test1 ≡ test4 = qed

val exp : nat ⇒ nat ⇒ nat = exp_ring semi_nat

val test_binome2 : ∀x y∈nat, (x + y) ** 2 ≡ x ** 2 + 2 * x * y + y ** 2 =
  fun a b {
    let x = Var[0];
    let y = Var[1];
    let env : nat ⇒ nat = fun v { case v { Zero → a | S[p] → b } };
    use eval_cor semi_nat ((x +~ y) **~ 2) env;
    use eval_cor semi_nat (x **~ 2 +~ Cst[2] *~ x *~ y +~ y **~ 2) env;
    qed
  }

val test_binome3 : ∀x y∈nat, (x + y) ** 3 ≡ x ** 3 + 3 * x ** 2 * y
                     + 3 * x * y ** 2 + y ** 3 =
  fun a b {
    let x = Var[0];
    let y = Var[1];
    let env : nat ⇒ nat = fun v { case v { Zero → a | S[p] → b } };
    use eval_cor semi_nat ((x +~ y) **~ 3) env;
    use eval_cor semi_nat (x **~ 3 +~ Cst[3] *~ x **~ 2 *~ y
                              +~ Cst[3] *~ x *~ y **~ 2 +~ y **~ 3) env;
    qed
  }


val test_binome4 : ∀x y∈nat, (x + y) ** 4 ≡ x ** 4 + 4 * x ** 3 * y
                     + 6 * x ** 2 * y ** 2 + 4 * x * y ** 3 + y ** 4 =
  fun a b {
    let x = Var[0];
    let y = Var[1];
    let env : nat ⇒ nat = fun v { case v { Zero → a | S[p] → b } };
    use eval_cor semi_nat ((x +~ y) **~ 4) env;
    use eval_cor semi_nat (x **~ 4 +~ Cst[4] *~ x **~ 3 *~ y
                              +~ Cst[6] *~ x **~ 2 *~ y **~ 2
                              +~ Cst[4] *~ x *~ y **~ 3 +~ y **~ 4) env;
    qed
  }

val test_binome5 : ∀x y∈nat, (x + y) ** 5 ≡ x ** 5 + 5 * x ** 4 * y
                     + 10 * x ** 3 * y ** 2 + 10 * x ** 2 * y ** 3
                     + 5 * x * y ** 4 + y ** 5 =
  fun a b {
    let x = Var[0];
    let y = Var[1];
    let env : nat ⇒ nat = fun v { case v { Zero → a | S[p] → b } };
    use eval_cor semi_nat ((x +~ y) **~ 5) env;
    use eval_cor semi_nat (x **~ 5 +~ Cst[5] *~ x **~ 4 *~ y
                     +~ Cst[10] *~ x **~ 3 *~ y **~ 2 +~ Cst[10] *~ x **~ 2 *~ y **~ 3
                     +~ Cst[5] *~ x *~ y **~ 4 +~ y **~ 5) env;
    qed
  }
