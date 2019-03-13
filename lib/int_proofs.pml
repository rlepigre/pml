include lib.int

// FIXME #30: auto fails because two cases are impossible by typing
// because p is positive below.
val suc_pre : ∀n∈int, suc (pre n) ≡ n = fun n {
  case n {
    Zero → {}
    S[p] → ncase⟨p⟩
    P[_] → {}
  }
}
val pre_suc : ∀n∈int, pre (suc n) ≡ n = fun n {
  case n {
    Zero → {}
    S[_] → {}
    P[p] → pcase⟨p⟩
  }
}

val rec add_zero_right : ∀n∈int, n + Zero ≡ n = fun n {
  case n {
    Zero → {}
    S[p] → eqns p + Zero ≡ p by add_zero_right p;
           showing suc(p+Zero) ≡ S[p];
           case p { //FIXME #30 too
             Zero → {}
             S[_] → {}
           }
    P[s] → eqns s + Zero ≡ s by add_zero_right s;
           showing pre(s+Zero) ≡ P[s];
           //showing suc(s+Zero) ≡ S[s]; // FIXME: wrong but loops!
           case s { //FIXME #30 too
             Zero → {}
             P[_] → {}
           }
  }
}

val rec add_succ_right : ∀n∈ int, ∀m∈pos, n + S[m] ≡ suc(n + m) = fun n m {
  case n {
    Zero → showing S[m] ≡ suc(m);
           case m { //FIXME #30 too
             Zero → {}
             S[_] → {}
           }
    S[p] → eqns p + S[m] ≡ suc(p + m) by add_succ_right p m;
           showing p + S[m] ≡ suc(p + m);
           {}
    P[s] → eqns s + S[m] ≡ suc(s + m) by add_succ_right s m;
           showing pre(suc(s + m)) ≡ suc(pre(s + m));
           pre_suc (s + m); suc_pre(s + m)
  }
}

val rec add_pre_right : ∀n∈ int, ∀m∈neg, n + P[m] ≡ pre(n + m) = fun n m {
  case n {
    Zero → showing P[m] ≡ pre(m);
           case m { //FIXME #30 too
             Zero → {}
             P[_] → {}
           }
    S[p] → eqns p + P[m] ≡ pre(p + m) by add_pre_right p m;
           showing suc(pre(p + m)) ≡ pre(suc(p + m));
           use pre_suc (p + m); use suc_pre(p + m)
    P[s] → eqns s + P[m] ≡ pre(s + m) by add_pre_right s m;
           showing s + P[m] ≡ pre(s + m);
           {}
  }
}

val rec add_commutative : ∀n m∈int, n + m ≡ m + n = fun n m {
  case n {
    Zero → add_zero_right m
    S[p] → add_succ_right m p; add_commutative p m
    P[s] → add_pre_right m s; add_commutative s m
  }
}