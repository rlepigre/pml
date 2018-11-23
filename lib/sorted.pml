include lib.bool
include lib.list
include lib.list_proofs

// Definition of the “is sorted” predicate on lists.
val rec is_sorted : ∀a, (a ⇒ a ⇒ bool) ⇒ list⟨a⟩ ⇒ bool =
  fun leq l {
    case l {
      []   → true
      x::l →
        case l {
          []   → true
          y::_ → leq x y && is_sorted leq l
        }
    }
  }

// If a list is sorted, its first two elements are in the right order.
val sorted_ineq : ∀a, ∀leq∈(a⇒a⇒bool), ∀x y∈a, ∀l∈list⟨a⟩,
    is_sorted leq (x::y::l) ⇒ leq x y =
  fun leq x y l _ {
    deduce is_sorted leq (x::y::l);
    if leq x y { qed } else { ✂ }
  }

// If a list is sorted, then its tail is also sorted.
val sorted_tail : ∀a, ∀leq∈(a⇒a⇒bool), ∀p∈a, ∀l∈list⟨a⟩,
    is_sorted leq (p::l) ⇒ is_sorted leq l =
  fun leq p l _ {
    deduce is_sorted leq (p::l);
    case l {
      []    →
        showing is_sorted leq [];
        qed
      x::xs →
        showing is_sorted leq (x::xs);
        deduce is_sorted leq (p::x::xs);
        show leq p x using sorted_ineq leq p x xs {};
        deduce is_sorted leq (x::xs);
        qed
    }
  }

// Any suffix of a sorted list is sorted.
val rec sorted_suffix : ∀a, ∀leq∈(a⇒a⇒bool), ∀l1 l2∈list⟨a⟩,
    is_sorted leq (l1 @ l2) ⇒ is_sorted leq l2 =
  fun leq l1 l2 _ {
    case l1 {
      []   → qed
      x::l →
        deduce is_sorted leq ((x::l) @ l2);
        deduce is_sorted leq (x::(l @ l2));
        show is_sorted leq (l @ l2) using sorted_tail leq x (l @ l2) {};
        use sorted_suffix leq l l2 {}
    }
  }

// Any prefix of a sorted list is sorted.
val rec sorted_prefix : ∀a, ∀leq∈(a⇒a⇒bool), ∀l1 l2∈list⟨a⟩,
    is_sorted leq (l1 @ l2) ⇒ is_sorted leq l1 =
  fun leq l1 l2 _ {
    case l1 {
      []     →
        deduce is_sorted leq [];
        qed
      x1::xs →
        deduce is_sorted leq ((x1::xs) @ l2);
        deduce is_sorted leq (x1::(xs @ l2));
        show is_sorted leq (xs @ l2) using sorted_tail leq x1 (xs @ l2) {};
        show is_sorted leq xs using sorted_prefix leq xs l2 {};
        showing is_sorted leq (x1::xs);
        case xs {
          []     →
            deduce is_sorted leq (x1::[]);
            qed
          x2::xs →
            deduce is_sorted leq ((x1::x2::xs) @ l2);
            deduce is_sorted leq (x1::x2::(xs @ l2));
            show leq x1 x2 using sorted_ineq leq x1 x2 (xs @ l2) {};
            qed
        }
    }
  }

// Removing an element of a sorted list yields a sorted list.
//val rec sorted_remove : ∀a, ∀leq∈(a⇒a⇒bool), ∀l1∈list⟨a⟩, ∀p∈a, ∀l2∈list⟨a⟩,
//    is_sorted leq (l1 @ (p::l2)) ⇒ is_sorted leq (l1 @ l2) =
//  fun leq l1 p l2 _ {
//    case l1 {
//      []    →
//        showing is_sorted leq l2;
//        deduce is_sorted leq (p::l2);
//        use sorted_tail leq p l2 {}
//      x::xs →
//        showing is_sorted leq ((x::xs) @ l2);
//        showing is_sorted leq (x::(xs @ l2));
//        deduce is_sorted leq ((x::xs) @ (p::l2));
//        deduce is_sorted leq (x::(xs @ (p::l2)));
//        show is_sorted leq (xs @ (p::l2)) using {
//          {- FIXME -}
//          //sorted_tail leq x (xs @ (p::l2)) {}
//        };
//        show is_sorted leq (xs @ l2) using sorted_remove leq xs p l2 {};
//        case xs {
//          []    →
//            showing is_sorted leq (x :: l2);
//            case l2 {
//              []    → qed
//              z::zs →
//                showing is_sorted leq (x::z::zs);
//                showing leq x z;
//                {- TODO -}
//            }
//          y::ys →
//            showing is_sorted leq ((x::y::ys) @ l2);
//            showing is_sorted leq (x::y::(ys @ l2));
//            deduce is_sorted leq ((x::y::ys) @ (p::l2));
//            show is_sorted leq (x::y::ys)
//              using sorted_prefix leq (x::y::ys) (p::l2) {};
//            use sorted_ineq leq x y ys {}
//        }
//    }
//  }
