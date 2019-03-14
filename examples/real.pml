include lib.int

type digit = [P; Z; S]

type sinter⟨s⟩ = ν_s inter, {} ⇒ digit × inter
type inter = sinter⟨∞⟩

val d2i : digit ⇒ int = fun n {
  case n {
    P → n1
    Z → p0
    S → p1
  }
}

val rec average' : ∀s, int ⇒ sinter⟨s+ₒ1⟩ ⇒ sinter⟨s+ₒ1⟩ ⇒ sinter⟨s⟩ =
  fun c a b _ {
    let (a0,a') = a {};
    let (b0,b') = b {};
    let d' = add (dbl c) (add (d2i a0) (d2i b0));
    if even d' {
      (sgn d', average' Zero a' b')
    } else {
      let (a1,a'') = a' {};
      let (b1,b'') = b' {};
      let d = add (dbl d') (add (d2i a1) (d2i b1));
      let e : digit = if ge d p2 { S } else { if le d n2 { P } else { Z } };
      let c' = d' - (dbl (d2i e));
      (e, average' c' a' b')
    }
  }

val average : ∀s, sinter⟨s+ₒ1⟩ ⇒ sinter⟨s+ₒ1⟩ ⇒ sinter⟨s⟩ = average' Zero

val oppD : digit ⇒ digit = fun d {
  case d {
    Z → Z
    S → P
    P → S
  }
}

val rec opp : ∀s, sinter⟨s⟩ ⇒ sinter⟨s⟩ = fun a _ {
  let (a0,a') = a {};
  (oppD a0, opp a')
}

val mulD : digit ⇒ digit ⇒ digit = fun a1 b1 {
  case a1 {
    Z → Z
    S → b1
    P → oppD b1
  }
}

val rec mulDI : ∀s, digit ⇒ sinter⟨s⟩ ⇒ sinter⟨s⟩ = fun a1 b _ {
  let (b1,b') = b {};
  (mulD a1 b1, mulDI a1 b')
}

// work in progress ⋯
// (1/2 x0 + 1/2 x) * y = 1/2 x0*y + 1/2 x*y = av(x0*y, x*y)
// (1/2 x0 + 1/2 x) * (1/2 y0 + 1/2 y)
//    = 1/4 x0 y0 + 1/4 (x0 y + y0 x) + 1/4 x y
//    = av(av(x0 y, y0 x), 1/2 x0 y0 + 1/2 x y)
// (x0 + 1/2x1 + 1/4 x) * (y0 + 1/2 y1 + 1/4 y) =
//    x0 y0 + 1/2 x0 y1 + 1/2 x1 y0 + 1/4 x1 y1 + 1/4 x0 y + 1/4 y0 x  +
//    1/8 x1 y + 1/8 x y1 +
// val rec mulI : ∀s, sinter⟨s+3⟩ → sinter⟨s+3⟩ → sinter⟨s⟩ =
//    fun a b {
//      let s such that _ : sinter⟨s⟩;
//      fun _ {
//        let (a0,a')  = a {}; //a' ⇒ s+2
//        let (b0,b')  = b {}; //b' ⇒ s+2
//        let p : sinter⟨s+1⟩ = average (mulDI b0 (a':sinter⟨s+2⟩))
//                                      (mulDI a0 (b':sinter⟨s+2⟩));
//        let q : sinter⟨s⟩ = fun _ { (mulD a0 b0,
//          (let s' such that _ : sinter⟨s'⟩;
//           mulI (a':sinter⟨s'+3⟩) (b':sinter⟨s'+3⟩))) };
//        average p q {}
//      }
//   }
