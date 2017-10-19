include lib.int

type digit = [P; Z; S]
type sinter⟨s⟩ = ν_s inter, {} ⇒ digit × inter

val d2i : digit ⇒ int = fun n {
  case n {
    P → pre Z
    Z → Z
    S → suc Z
  }
}

// FIXME: uncaught exception not found
// val rec average' : ∀s, int ⇒ sinter⟨s+1+1⟩ ⇒ sinter⟨s+1+1⟩ ⇒ sinter⟨s+1⟩ =
//   fun c a b _ {
//     let (a0,a') = a {};
//     let (b0,b') = b {};
//     let d' = add (dbl c) (add (d2i a0) (d2i b0));
//     if even d' {
//       (sgn d', average' Z a' b')
//     } else {
//       let (a1,a'') = a' {};
//       let (b1,b'') = b' {};
//       let d = add (dbl d') (add (d2i a1) (d2i b1));
//       let e = if ge d p2 { S } else { if le d n2 { P } else { Z } };
//       let c' = sub d' (dbl (d2i e));
//       (e, average' c' a' b')
//     }
//   }

// val average : ∀s, sinter⟨s+1+1⟩ ⇒ sinter⟨s+1+1⟩ ⇒ sinter⟨s+1⟩ = average' Z
