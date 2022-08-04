infix (*) = mul priority 2 left associative

// monoid with m as carrier type
type mono⟨m,e,(*)⟩ =
               { e  : e ∈ m             // we use singleton type to make e and op
               ; (*) : (*)∈(m ⇒ m ⇒ m)  // available in the rest of the record
               ; nl : ∀a∈m, e * a ≡ a   // a syntactic sugar should hide this
               ; nr : ∀a∈m, a * e ≡ a
               ; as : ∀a b c∈m, a * (b * c) ≡ (a * b) * c
               }

// the type of all monoid
type monoid = ∃m,∃e,∃(*), mono⟨m,e,(*)⟩

val product : ∀m1 m2 ∈ monoid, monoid =
  fun m1 m2 {
    let e1 = m1.e; let e2 = m2.e;
    let x1 such that e1 : e1 ∈ x1;
    let x2 such that e2 : e2 ∈ x2;
    let (*) : x1 × x2 ⇒ x1 × x2 ⇒ x1 × x2 =
      fun a b { (a.1 *_m1 b.1, a.2 *_m2 b.2) };
    { e = ((m1.e, m2.e) : (m1.e, m2.e) ∈ (x1 × x2))
    , (*) = ((*) : (*) ∈ (x1 × x2 ⇒ x1 × x2 ⇒ x1 × x2))
    , nl = fun a { use m1.nl a.1;
                   use m2.nl a.2; qed }
    , nr = fun a { use m1.nr a.1;
                   use m2.nr a.2; qed }
    , as = fun a b c {
                  use m1.as a.1 b.1 c.1;
                  use m2.as a.2 b.2 c.2;
                  set auto 0 2; qed }
    }
  }