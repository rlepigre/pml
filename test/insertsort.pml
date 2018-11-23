include lib.bool
include lib.nat
include lib.order
include lib.list
include lib.nat_proofs
include lib.list_proofs
include lib.sorted

// Implementation of insertion sort.

val rec insert : ∀a, total_order⟨a⟩ ⇒ a ⇒ list⟨a⟩ ⇒ list⟨a⟩ =
  fun o e l {
    case l {
      []     → e :: []
      hd::tl → if o.cmp e hd { e :: l } else { hd :: (insert o e tl) }
    }
  }

val rec isort : ∀a, total_order⟨a⟩ ⇒ list⟨a⟩ ⇒ list⟨a⟩ =
  fun o l {
    case l {
      []     → []
      hd::tl → insert o hd (isort o tl)
    }
  }

// Some tests.

val u0 : nat = zero
val u1 : nat = succ u0
val u2 : nat = succ u1
val u3 : nat = succ u2
val u4 : nat = succ u3
val u5 : nat = succ u4
val u6 : nat = succ u5
val u7 : nat = succ u6
val u8 : nat = succ u7
val u9 : nat = succ u8

val test : {} =
  let l : list⟨nat⟩ = (u3::u7::u1::u2::u9::u0::u0::u1::[]);
  print "isort ";
  println_list print_nat l;
  print "    = ";
  println_list print_nat (isort nat_order l)


// Prove that the produced list is sorted.

val rec insert_sorted : ∀a, ∀o∈total_order⟨a⟩, ∀e∈a, ∀l∈list⟨a⟩,
    is_sorted o.cmp l ⇒ is_sorted o.cmp (insert o e l) =
  fun o e l _ {
    case l {
      []     →
        showing is_sorted o.cmp (insert o e []);
        showing is_sorted o.cmp (e::[]);
        qed
      hd::tl →
        showing is_sorted o.cmp (insert o e (hd::tl));
        show is_sorted o.cmp tl using sorted_tail o.cmp hd tl {};
        show is_sorted o.cmp (insert o e tl) using insert_sorted o e tl {};
        if o.cmp e hd { qed } else {
          show o.cmp hd e using o.total e hd;
          showing is_sorted o.cmp (hd :: insert o e tl);
          case tl {
            []         →
              showing is_sorted o.cmp (hd :: insert o e []);
              showing is_sorted o.cmp (hd :: e :: []);
              qed
            hdtl::tltl →
              showing is_sorted o.cmp (hd :: insert o e (hdtl::tltl));
              show o.cmp hd hdtl using sorted_ineq o.cmp hd hdtl tltl {};
              if o.cmp e hdtl { qed } else {
                show o.cmp hdtl e using o.total e hdtl;
                qed
              }
          }
        }
    }
  }

val rec isort_sorts : ∀a, ∀o∈total_order⟨a⟩, ∀l∈list⟨a⟩,
    is_sorted o.cmp (isort o l) =
  fun o l {
    case l {
      []     →
        showing is_sorted o.cmp (isort o []);
        showing is_sorted o.cmp [];
        qed
      hd::tl →
        showing is_sorted o.cmp (isort o (hd::tl));
        showing is_sorted o.cmp (insert o hd (isort o tl));
        show is_sorted o.cmp (isort o tl) using isort_sorts o tl;
        use insert_sorted o hd (isort o tl) {};
        qed
    }
  }

// Prove that the elements are preserved.

val rec count : ∀a, (a⇒a⇒bool) ⇒ a ⇒ list⟨a⟩ ⇒ nat =
  fun cmp x l {
    case l {
      []   → zero
      y::l → if cmp x y && cmp y x { S[count cmp x l] }
             else { count cmp x l }
    }
  }

// Could add hypothesis that l is sorted.

val rec lemma1 : ∀a, ∀o∈total_order⟨a⟩, ∀x∈a, ∀e∈a, ∀l∈list⟨a⟩,
    o.cmp x e && o.cmp e x ⇒
    S[count o.cmp x l] ≡ count o.cmp x (insert o e l) =
  fun o x e l _ {
    case l {
      []     → qed
      hd::tl →
        if o.cmp e hd {
          showing S[count o.cmp x (hd::tl)]
                ≡ count o.cmp x (e::hd::tl);
          qed
        } else {
          show S[count o.cmp x tl] ≡ count o.cmp x (insert o e tl)
            using lemma1 o x e tl {};
          showing S[count o.cmp x (hd::tl)]
                ≡ count o.cmp x (hd::insert o e tl);
          if o.cmp x hd && o.cmp hd x {
            showing S[S[count o.cmp x tl]]
                  ≡ S[count o.cmp x (insert o e tl)];
            showing S[count o.cmp x tl]
                  ≡ count o.cmp x (insert o e tl);
            qed
          } else {
            showing S[count o.cmp x tl]
                  ≡ count o.cmp x (insert o e tl);
            qed
          }
        } 
    }
  }

val rec lemma2 : ∀a, ∀o∈total_order⟨a⟩, ∀x∈a, ∀e∈a, ∀l∈list⟨a⟩,
    (o.cmp x e && o.cmp e x ⇒ ∀x,x) ⇒
    count o.cmp x l ≡ count o.cmp x (insert o e l) =
  fun o x e l absurd {
    if o.cmp x e && o.cmp e x { absurd {} } else {
      case l {
        []     →
          showing count o.cmp x [] ≡ count o.cmp x (insert o e []);
          showing count o.cmp x [] ≡ count o.cmp x (e::[]);
          qed
        hd::tl →
          showing count o.cmp x (hd::tl)
                ≡ count o.cmp x (insert o e (hd::tl));
          if o.cmp e hd {
            showing count o.cmp x (hd::tl)
                  ≡ count o.cmp x (e::hd::tl);
            qed
          } else {
            show count o.cmp x tl ≡ count o.cmp x (insert o e tl)
              using lemma2 o x e tl absurd;
            showing count o.cmp x (hd::tl)
                  ≡ count o.cmp x (hd::insert o e tl);
            if o.cmp x hd && o.cmp hd x {
              showing S[count o.cmp x tl]
                    ≡ S[count o.cmp x (insert o e tl)];
              showing count o.cmp x tl
                    ≡ count o.cmp x (insert o e tl);
              qed
            } else {
              showing count o.cmp x tl
                    ≡ count o.cmp x (insert o e tl);
              qed
            }
          }
      }
    }
  }

val rec theorem : ∀a, ∀o∈total_order⟨a⟩, ∀e∈a, ∀l∈list⟨a⟩,
    count o.cmp e l ≡ count o.cmp e (isort o l) =
  fun o e l {
    case l {
      []     →
        showing count o.cmp e [] ≡ count o.cmp e (isort o []);
        showing count o.cmp e [] ≡ count o.cmp e [];
        qed
      hd::tl → 
        show count o.cmp e tl ≡ count o.cmp e (isort o tl)
          using theorem o e tl;
        showing count o.cmp e (hd::tl)
              ≡ count o.cmp e (isort o (hd::tl));
        if o.cmp e hd && o.cmp hd e {
          showing S[count o.cmp e tl]
                ≡ count o.cmp e (isort o (hd::tl));
          showing S[count o.cmp e (isort o tl)]
                ≡ count o.cmp e (isort o (hd::tl));
          showing S[count o.cmp e (isort o tl)]
                ≡ count o.cmp e (insert o hd (isort o tl));
          use lemma1 o e hd (isort o tl) {}
        } else {
          showing count o.cmp e tl
                ≡ count o.cmp e (isort o (hd::tl));
          showing count o.cmp e (isort o tl)
                ≡ count o.cmp e (isort o (hd::tl));
          showing count o.cmp e (isort o tl)
                ≡ count o.cmp e (insert o hd (isort o tl));
          let absurd : o.cmp e hd && o.cmp hd e ⇒ ∀x,x = fun _ { ✂ };
          use lemma2 o e hd (isort o tl) absurd
        }
    }
  }

