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
           //showing suc(s+Zero) ≡ S[s]; // FIXME #24: wrong but loops,
              //probably a cyclic value in the pool!
           case s { //FIXME #30 too
             Zero → {}
             P[_] → {}
           }
  }
}

val rec add_S_right : ∀n∈ int, ∀m∈pos, n + S[m] ≡ suc(n + m) = fun n m {
  case n {
    Zero → showing S[m] ≡ suc(m);
           case m { //FIXME #30 too
             Zero → {}
             S[_] → {}
           }
    S[p] → eqns p + S[m] ≡ suc(p + m) by add_S_right p m;
           showing p + S[m] ≡ suc(p + m);
           {}
    P[s] → eqns s + S[m] ≡ suc(s + m) by add_S_right s m;
           showing pre(suc(s + m)) ≡ suc(pre(s + m));
           pre_suc (s + m); suc_pre(s + m)
  }
}

val rec add_P_right : ∀n∈ int, ∀m∈neg, n + P[m] ≡ pre(n + m) = fun n m {
  case n {
    Zero → showing P[m] ≡ pre(m);
           case m { //FIXME #30 too
             Zero → {}
             P[_] → {}
           }
    S[p] → eqns p + P[m] ≡ pre(p + m) by add_P_right p m;
           showing suc(pre(p + m)) ≡ pre(suc(p + m));
           use pre_suc (p + m); use suc_pre(p + m)
    P[s] → eqns s + P[m] ≡ pre(s + m) by add_P_right s m;
           showing s + P[m] ≡ pre(s + m);
           {}
  }
}

val rec add_commutative : ∀n m∈int, n + m ≡ m + n = fun n m {
  case n {
    Zero → add_zero_right m
    S[p] → add_S_right m p; add_commutative p m
    P[s] → add_P_right m s; add_commutative s m
  }
}

val add_suc_left : ∀n m∈int, suc n + m ≡ suc (n + m) = fun n m {
  case n {
    Zero → {}
    S[p] → {}
    P[s] → suc_pre (s + m)
  }
}

val add_pre_left : ∀n m∈int, pre n + m ≡ pre (n + m) = fun n m {
  case n {
    Zero → {}
    S[p] → pre_suc (p + m)
    P[s] → {}
  }
}

val rec add_associative : ∀m n p∈int, (m + n) + p ≡ m + (n + p) =
  fun m n q {
    case m {
      Zero → {}
      S[p] → add_suc_left (p + n) q; add_associative p n q
      P[s] → add_pre_left (s + n) q; add_associative s n q
    }
  }

val rec opp_pos_idempotent : ∀n∈pos, opp_neg (opp_pos n) ≡ n = fun n {
  case n {
    Zero → {}
    S[p] → opp_pos_idempotent p
  }
}

val rec opp_neg_idempotent : ∀n∈neg, opp_pos (opp_neg n) ≡ n = fun n {
  case n {
    Zero → {}
    P[p] → opp_neg_idempotent p
  }
}

val opp_idempotent : ∀n∈int, opp (opp n) ≡ n = fun n {
  case n {
    Zero → {}
    S[p] → opp_pos_idempotent p
    P[s] → opp_neg_idempotent s
  }
}

val rec add_opp_pos : ∀n∈int, ∀m∈pos, n + opp_pos m ≡ n - m = fun n m {
  case m {
    Zero → add_zero_right n
    S[p] → add_P_right n (opp_pos p); add_opp_pos n p
  }
}

val rec add_opp_neg : ∀n∈int, ∀m∈neg, n + opp_neg m ≡ n - m = fun n m {
  case m {
    Zero → add_zero_right n
    P[s] → add_S_right n (opp_neg s); add_opp_neg n s
  }
}

 val add_opp : ∀n m∈int, n + opp m ≡ n - m = fun n m {
   case m {
     Zero → add_zero_right n
     S[p] → add_P_right n (opp_pos p); add_opp_pos n p
     P[s] → add_S_right n (opp_neg s); add_opp_neg n s
   }
 }

val rec opp_pos_suc : ∀n∈pos, opp_pos (suc n) ≡ pre (opp_pos n) = fun n {
  case n {
    Zero → {}
    S[p] → opp_pos_suc p
  }
}

val rec opp_neg_pre : ∀n∈neg, opp_neg (pre n) ≡ suc (opp_neg n) = fun n {
  case n {
    Zero → {}
    P[s] → opp_neg_pre s
  }
}

val opp_suc : ∀n∈int, opp (suc n) ≡ pre (opp n) = fun n {
  case n {
    Zero → {}
    S[p] → opp_pos_suc p
    P[s] → showing opp s ≡ pre S[opp_neg s]; case s { Zero → {} P[_] → {} }
  }
}

val opp_pre : ∀n∈int, opp (pre n) ≡ suc (opp n) = fun n {
  case n {
    Zero → {}
    S[p] → showing opp p ≡ suc P[opp_pos p]; case p { Zero → {} S[_] → {} }
    P[s] → opp_neg_pre s
  }
}

val rec add_opp_opp : ∀n m∈int, opp n + opp m ≡ opp (n + m) = fun n m {
  case n {
    Zero → {}
    S[p] → showing P[opp_pos p] + opp m ≡  opp (suc (p + m));
           opp_suc (p + m);
           showing P[opp_pos p] + opp m ≡  pre (opp (p + m));
           eqns opp_pos p ≡ opp p by case p { Zero → {} S[_] → {} };
           add_opp_opp p m;
           {}
    P[s] → showing S[opp_neg s] + opp m ≡  opp (pre (s + m));
           opp_pre (s + m);
           showing S[opp_neg s] + opp m ≡  suc (opp (s + m));
           eqns opp_neg s ≡ opp s by case s { Zero → {} P[_] → {} };
           add_opp_opp s m;
           {}
  }
}

val rec sub_associative : ∀m n p∈int, (m - n) - p ≡ m - (n + p) =
  fun m n p {
    add_opp m n; add_opp (m - n) p; add_opp m (n + p);
    add_opp_opp n p;
    add_associative m (opp n) (opp p)
  }

val rec sub_associative2 : ∀m n p∈int, m - (n - p) ≡ (m - n) + p =
  fun m n p {
    add_opp m n; add_opp n p; add_opp m (n - p);
    add_opp_opp n (opp p); opp_idempotent p;
    add_associative m (opp n) p;
    {}
  }

val rec sub_associative3 : ∀m n p∈int, m + (n - p) ≡ (m + n) - p =
  fun m n p {
    add_opp n p; add_opp (m + n) p;
    add_associative m n (opp p);
    {}
  }