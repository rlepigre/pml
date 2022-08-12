include lib.int

val suc_pre : ∀n∈int, suc (pre n) ≡ n = fun n {
  set auto 2 1; {}
}

val pre_suc : ∀n∈int, pre (suc n) ≡ n = fun n {
  set auto 2 1; {}
}

val rec add_zero_right : ∀n∈int, n + Zero ≡ n = fun n {
  case n {
    Zero → {}
    S[p] → show p + Zero ≡ p by add_zero_right p;
           showing suc(p+Zero) ≡ S[p];
           set auto 1 0; {}
    P[s] → show s + Zero ≡ s by add_zero_right s;
           showing pre(s+Zero) ≡ P[s];
           set auto 1 0; {}
           //showing suc(s+Zero) ≡ S[s]; // FIXME #24: wrong but loops,
              //probably a cyclic value in the pool!
  }
}

val rec add_S_right : ∀n∈ int, ∀m∈pos, n + S[m] ≡ suc(n + m) = fun n m {
  case n {
    Zero → showing S[m] ≡ suc(m);
           set auto 1 0; {}
    S[p] → show p + S[m] ≡ suc(p + m) by add_S_right p m;
           showing p + S[m] ≡ suc(p + m);
           {}
    P[s] → show s + S[m] ≡ suc(s + m) by add_S_right s m;
           showing pre(suc(s + m)) ≡ suc(pre(s + m));
           pre_suc (s + m); suc_pre(s + m)
  }
}

val rec add_P_right : ∀n∈ int, ∀m∈neg, n + P[m] ≡ pre(n + m) = fun n m {
  case n {
    Zero → showing P[m] ≡ pre(m);
           set auto 1 0; {}
    S[p] → show p + P[m] ≡ pre(p + m) by add_P_right p m;
           showing suc(pre(p + m)) ≡ pre(suc(p + m));
           use pre_suc (p + m); use suc_pre(p + m)
    P[s] → show s + P[m] ≡ pre(s + m) by add_P_right s m;
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

val rec add_inv : ∀m∈int, m + opp m ≡ Zero = fun m {
  case m {
    Zero → {}
    S[p] → show m + opp m
           ≡ suc (pre (p + opp_pos p)) by add_P_right p (opp_pos p)
           ≡ suc (pre (p + opp p)) by (case p {Zero → {} S[_] → {}})
           ≡ p + opp p by suc_pre (p + opp p);
           add_inv p
    P[s] → show m + opp m
           ≡ pre (suc (s + opp_neg s)) by add_S_right s (opp_neg s)
           ≡ pre (suc (s + opp s)) by (case s {Zero → {} P[_] → {}})
           ≡ s + opp s by pre_suc (s + opp s);
           add_inv s
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

val add_inv2 : ∀m∈int, m - m ≡ Zero = fun m { add_inv m; add_opp m m }


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
    P[s] → set auto 1 1; {}
  }
}

val opp_pre : ∀n∈int, opp (pre n) ≡ suc (opp n) = fun n {
  case n {
    Zero → {}
    S[p] → set auto 1 1; {}
    P[s] → opp_neg_pre s
  }
}

val rec add_opp_opp : ∀n m∈int, opp n + opp m ≡ opp (n + m) = fun n m {
  case n {
    Zero → {}
    S[p] → showing P[opp_pos p] + opp m ≡  opp (suc (p + m));
           opp_suc (p + m);
           showing P[opp_pos p] + opp m ≡  pre (opp (p + m));
           add_opp_opp p m;
           set auto 1 1; {}
    P[s] → showing S[opp_neg s] + opp m ≡  opp (pre (s + m));
           opp_pre (s + m);
           showing S[opp_neg s] + opp m ≡  suc (opp (s + m));
           add_opp_opp s m;
           set auto 1 1; {}
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

val rec non_neg_add : ∀m n∈{ x ∈ int | non_negative x}, non_negative (m + n)
  = fun m n {
    case m {
      Zero  → {}
      S[pm] → show non_negative pm using (set auto 1 0; {});
              non_neg_add pm n; set auto 1 1; {}
      P[sm] → ✂
    }
  }

val rec add_increasing : ∀m n p q∈int, le m n ⇒ le p q ⇒ le (m + p) (n + q) =
  fun m n p q _ _ {
    showing non_negative ((n + q) - (m + p));
    show (n + q) - (m + p)
      ≡ n + (q - (m + p)) by sub_associative3 n q (m + p)
      ≡ n + ((q - m) - p) by sub_associative  q m p
      ≡ n + ((opp m + q) - p) by (add_opp q m; add_commutative (opp m) q)
      ≡ n + (opp m + (q - p)) by sub_associative3 (opp m) q p
      ≡ (n - m) + (q - p) by (add_associative n (opp m) (q - p); add_opp n m);
    deduce non_negative (n - m);
    deduce non_negative (q - p);
    non_neg_add (n - m) (q - p)
  }

val le_reflexive : ∀m∈int, le m m = fun m { add_inv2 m }

val not_le_is_gt : ∀m n∈int, le m n ≡ false ⇒ gt m n = fun m n _ {
  show n - m ≡ opp (m - n) by (add_opp n m; add_opp m n;
                               add_commutative n (opp m);
                               add_opp_opp m (opp n); opp_idempotent n);

  case (m - n) {
    Zero → ✂
    S[_] → {}
    P[x] → let c = opp_neg x; // fixme #28 incompleteness of auto
           ✂
  }
}

val lt_is_le : ∀m n∈int, lt m n ⇒ le m n = fun m n _ {
  let c = n - m; // fixme #28 incompleteness of auto
  set auto 2 2; qed
}

val not_ge_is_lt : ∀m n∈int, ge m n ≡ false ⇒ lt m n =
  fun m n { not_le_is_gt n m }

val gt_is_ge : ∀m n∈int, gt m n ⇒ ge m n = fun m n { lt_is_le n m }


val rec add_increasing_left : ∀m n p∈int, le m n ⇒ le (m + p) (n + p) =
  fun m n p _ {
    le_reflexive p; add_increasing m n p p {} {}
  }

val rec add_increasing_right : ∀m n p∈int, le m n ⇒ le (p + m) (p + n) =
  fun m n p _ {
    le_reflexive p; add_increasing p p m n {} {}
  }
