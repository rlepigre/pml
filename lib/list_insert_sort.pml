include lib.bool
include lib.order
include lib.nat
include lib.nat_proofs
include lib.list
include lib.list_proofs
include lib.list_sorted
include lib.list_count

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

val rec insert_sorted : ∀a, ∀o∈total_order⟨a⟩, ∀e∈a, ∀l∈slist⟨a,o⟩,
    sorted o (insert o e l) =
  fun o e l {
    case l {
      []     →
        showing sorted o (insert o e []);
        showing sorted o (e::[]);
        qed
      hd::tl →
        showing sorted o (insert o e (hd::tl));
        show sorted o tl using sorted_tail o hd tl {};
        show sorted o (insert o e tl) using insert_sorted o e tl;
        if o.cmp e hd { qed } else {
          show o.cmp hd e using o.total e hd;
          showing sorted o (hd :: insert o e tl);
          case tl {
            []         →
              showing sorted o (hd :: insert o e []);
              showing sorted o (hd :: e :: []);
              qed
            hdtl::tltl →
              showing sorted o (hd :: insert o e (hdtl::tltl));
              show o.cmp hd hdtl using sorted_ineq o hd hdtl tltl {};
              if o.cmp e hdtl { qed } else {
                show o.cmp hdtl e using o.total e hdtl;
                qed
              }
          }
        }
    }
  }

val rec isort_sorts : ∀a, ∀o∈total_order⟨a⟩, ∀l∈list⟨a⟩,
    sorted o (isort o l) =
  fun o l {
    case l {
      []     →
        showing sorted o (isort o []);
        showing sorted o [];
        qed
      hd::tl →
        showing sorted o (isort o (hd::tl));
        showing sorted o (insert o hd (isort o tl));
        show sorted o (isort o tl) using isort_sorts o tl;
        use insert_sorted o hd (isort o tl);
        qed
    }
  }

// We can redifine the sorting function to get a more precise type.

val other_isort : ∀a, ∀o∈total_order⟨a⟩, list⟨a⟩ ⇒ slist⟨a,o⟩ =
  fun o l {
    use isort_sorts o l;
    isort o l
  }

// Prove that the elements are preserved (we could add the hypothesis that
// the list we insert into is sorted. However, this is more general.

val rec insert_count : ∀a, ∀o∈total_order⟨a⟩, ∀x∈a, ∀e∈a, ∀l∈list⟨a⟩,
    o.cmp x e && o.cmp e x ⇒ S[count o x l] ≡ count o x (insert o e l) =
  fun o x e l _ {
    case l {
      []     → qed
      hd::tl →
        if o.cmp e hd {
          showing S[count o x (hd::tl)]
                ≡ count o x (e::hd::tl);
          qed
        } else {
          show S[count o x tl] ≡ count o x (insert o e tl)
            using insert_count o x e tl {};
          showing S[count o x (hd::tl)]
                ≡ count o x (hd::insert o e tl);
          if o.cmp x hd && o.cmp hd x {
            showing S[S[count o x tl]]
                  ≡ S[count o x (insert o e tl)];
            showing S[count o x tl]
                  ≡ count o x (insert o e tl);
            qed
          } else {
            showing S[count o x tl]
                  ≡ count o x (insert o e tl);
            qed
          }
        } 
    }
  }

val rec lemma2 : ∀a, ∀o∈total_order⟨a⟩, ∀x∈a, ∀e∈a, ∀l∈list⟨a⟩,
    (o.cmp x e && o.cmp e x ⇒ ∀x,x) ⇒
    count o x l ≡ count o x (insert o e l) =
  fun o x e l absurd {
    if o.cmp x e && o.cmp e x { absurd {} } else {
      case l {
        []     →
          showing count o x [] ≡ count o x (insert o e []);
          showing count o x [] ≡ count o x (e::[]);
          qed
        hd::tl →
          showing count o x (hd::tl)
                ≡ count o x (insert o e (hd::tl));
          if o.cmp e hd {
            showing count o x (hd::tl)
                  ≡ count o x (e::hd::tl);
            qed
          } else {
            show count o x tl ≡ count o x (insert o e tl)
              using lemma2 o x e tl absurd;
            showing count o x (hd::tl)
                  ≡ count o x (hd::insert o e tl);
            if o.cmp x hd && o.cmp hd x {
              showing S[count o x tl]
                    ≡ S[count o x (insert o e tl)];
              showing count o x tl
                    ≡ count o x (insert o e tl);
              qed
            } else {
              showing count o x tl
                    ≡ count o x (insert o e tl);
              qed
            }
          }
      }
    }
  }

val rec isort_count : ∀a, ∀o∈total_order⟨a⟩, ∀e∈a, ∀l∈list⟨a⟩,
    count o e l ≡ count o e (isort o l) =
  fun o e l {
    case l {
      []     →
        showing count o e [] ≡ count o e (isort o []);
        showing count o e [] ≡ count o e [];
        qed
      hd::tl → 
        show count o e tl ≡ count o e (isort o tl)
          using isort_count o e tl;
        showing count o e (hd::tl)
              ≡ count o e (isort o (hd::tl));
        if o.cmp e hd && o.cmp hd e {
          showing S[count o e tl]
                ≡ count o e (isort o (hd::tl));
          showing S[count o e (isort o tl)]
                ≡ count o e (isort o (hd::tl));
          showing S[count o e (isort o tl)]
                ≡ count o e (insert o hd (isort o tl));
          use insert_count o e hd (isort o tl) {}
        } else {
          showing count o e tl
                ≡ count o e (isort o (hd::tl));
          showing count o e (isort o tl)
                ≡ count o e (isort o (hd::tl));
          showing count o e (isort o tl)
                ≡ count o e (insert o hd (isort o tl));
          let absurd : o.cmp e hd && o.cmp hd e ⇒ ∀x,x = fun _ { ✂ };
          use lemma2 o e hd (isort o tl) absurd
        }
    }
  }
