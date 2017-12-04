include lib.bool

// Proof of the excluded middle
val excluded_middle : ∀x∈bool, or x (not x) =
  fun b {
    if b { {} } else { {} }
  }

// Equivalence is reflexive.
val eq_refl : ∀x∈bool, eq x x =
  fun b {
    if b { {} } else { {} }
  }

// Equivalence is commutative.
val eq_comm : ∀x y∈bool, eq x y ≡ eq y x =
  fun b1 b2 {
    if b1 { if b2 { {} } else { {} } } else { if b2 { {} } else { {} } }
  }

// The commutation of equivalence is equivalent.
val eq_comm2 : ∀x y∈bool, eq (eq x y) (eq y x) =
  fun b1 b2 {
    if b1 { if b2 { {} } else { {} } } else { if b2 { {} } else { {} } }
  }

// Equivalence is associative.
val eq_asso : ∀x y z∈bool, eq (eq x y) z ≡ eq x (eq y z) =
  fun b1 b2 b3 {
    if b1 {
      if b2 { if b3 { {} } else { {} } } else { if b3 { {} } else { {} } }
    } else {
      if b2 { if b3 { {} } else { {} } } else { if b3 { {} } else { {} } }
    }
  }

// Commutativity of equivalence using lemmas.
val eq_comm3 : ∀x y∈bool, eq (eq x y) (eq y x) =
  fun b1 b2 {
    show eq (eq b1 b2) (eq b1 b2) using eq_refl (eq b1 b2);
    show eq b1 b2 ≡ eq b2 b1 using eq_comm b1 b2;
    deduce eq (eq b1 b2) (eq b2 b1);
    qed
  }
