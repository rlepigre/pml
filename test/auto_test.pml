include lib.nat
include lib.bool

// Associativity of addition (detailed proof).
val rec add_assoc : ∀m n p∈nat, add m (add n p) ≡ add (add m n) p =
  fun m0 n0 p0 {
    //let _ = add n p;
    case m0 {
      Zero → qed
      S[k] → use (add_assoc k n0 p0);
             //let _ = add k n;
             qed
    }
  }

val taut0a : ∀a∈bool,  imp a a =
  fun a {
    case a {
      false → {}
      true  → {}
    }
  }

val taut0b : ∀a∈bool,  imp a a =
  take (a:bool);
  case a {
    false → {}
    true  → {}
  }

val taut0c : ∀a∈bool,  a ⇒ a =
  take (a:bool);
  suppose a;
  qed

val taut0d : ∀a∈bool,  imp a a =
  take (a:bool);
  assume a;
  showing a;
  qed

val taut1 : ∀a b c∈bool,  eq (imp (and a b) c) (imp a (imp b c)) =
  fun a b c { set auto 2 10; {} }

set auto 3 10

val taut2 : ∀a b c∈bool,  eq (eq (eq a b) c) (eq a (eq b c)) =
  fun a b c { {} }
