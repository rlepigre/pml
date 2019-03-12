include lib.bool
include lib.order
include lib.list
include lib.list_proofs

// Definition of the “is sorted” predicate on lists.
val rec sorted : ∀a, rel⟨a⟩ ⇒ list⟨a⟩ ⇒ bool =
  fun r l {
    case l {
      []   → true
      x::l →
        case l {
          []   → true
          y::_ → r.cmp x y && sorted r l
        }
    }
  }

// Type of sorted lists.
type slist⟨a,r⟩ = {l∈list⟨a⟩ | sorted r l }

// If a list is sorted, its first two elements are in the right order.
val sorted_ineq : ∀a, ∀r∈rel⟨a⟩, ∀x y∈a, ∀l∈list⟨a⟩,
    sorted r (x::y::l) ⇒ r.cmp x y =
  fun r x y l _ {
    deduce sorted r (x::y::l);
    if r.cmp x y { qed } else { ✂ }
  }

// If a list is sorted, then its tail is also sorted.
val sorted_tail : ∀a, ∀r∈rel⟨a⟩, ∀p∈a, ∀l∈list⟨a⟩,
    sorted r (p::l) ⇒ sorted r l =
  fun r p l _ {
    deduce sorted r (p::l);
    case l {
      []    →
        showing sorted r [];
        qed
      x::xs →
        showing sorted r (x::xs);
        deduce sorted r (p::x::xs);
        show r.cmp p x using sorted_ineq r p x xs {};
        deduce sorted r (x::xs);
        qed
    }
  }

// Any suffix of a sorted list is sorted.
val rec sorted_suffix : ∀a, ∀r∈rel⟨a⟩, ∀l1 l2∈list⟨a⟩,
    sorted r (l1 @ l2) ⇒ sorted r l2 =
  fun r l1 l2 _ {
    case l1 {
      []   → qed
      x::l →
        deduce sorted r ((x::l) @ l2);
        deduce sorted r (x::(l @ l2));
        show sorted r (l @ l2) using sorted_tail r x (l @ l2) {};
        use sorted_suffix r l l2 {}
    }
  }

// Any prefix of a sorted list is sorted.
val rec sorted_prefix : ∀a, ∀r∈rel⟨a⟩, ∀l1 l2∈list⟨a⟩,
    sorted r (l1 @ l2) ⇒ sorted r l1 =
  fun r l1 l2 _ {
    case l1 {
      []     →
        deduce sorted r [];
        qed
      x1::xs →
        deduce sorted r ((x1::xs) @ l2);
        deduce sorted r (x1::(xs @ l2));
        show sorted r (xs @ l2) using sorted_tail r x1 (xs @ l2) {};
        show sorted r xs using sorted_prefix r xs l2 {};
        showing sorted r (x1::xs);
        case xs {
          []     →
            deduce sorted r (x1::[]);
            qed
          x2::xs →
            deduce sorted r ((x1::x2::xs) @ l2);
            deduce sorted r (x1::x2::(xs @ l2));
            show r.cmp x1 x2 using sorted_ineq r x1 x2 (xs @ l2) {};
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
//          {- goal. -}
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
//                {- goal -}
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
