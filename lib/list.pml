include lib.option
include lib.nat

type rec list⟨a:ο⟩ = [Nil ; Cons of {hd : A ; tl : list⟨a⟩}]

val nil : ∀a, list⟨a⟩ = []
val cons : ∀a, a ⇒ list⟨a⟩ ⇒ list⟨a⟩ = fun hd tl { hd :: tl }

val head : ∀a, list⟨a⟩ ⇒ option⟨a⟩ =
  fun l {
    case l {
      []       → none
      hd :: tl → some hd
    }
  }

val tail : ∀a, list⟨a⟩ ⇒ option⟨list⟨a⟩⟩ =
  fun l {
    case l {
      []       → none
      hd :: tl → some tl
    }
  }

val rec length : ∀a, list⟨a⟩ ⇒ nat =
  fun l {
    case l {
      []       → zero
      hd :: tl → succ (length tl)
    }
  }

val rec map : ∀a b, (a ⇒ b) ⇒ list⟨a⟩ ⇒ list⟨b⟩ =
  fun fn l {
    case l {
      []       → []
      hd :: tl → fn hd :: map fn tl
    }
  }

val rec iter : ∀a, (a ⇒ {}) ⇒ list⟨a⟩ ⇒ {} =
  fun fn l {
    case l {
      []   → {}
      x::l → fn x; iter fn l
    }
  }

val rec iter2 : ∀a, (a → {}) ⇒ list⟨a⟩ → {} =
  fun fn l {
    case l {
      []   → {}
      x::l → fn x; iter2 fn l
    }
  }

val rec fold_left : ∀a b, (a ⇒ b ⇒ a) ⇒ a ⇒ list⟨b⟩ ⇒ a =
  fun fn acc l {
    case l {
      []       → acc
      hd :: tl → fold_left fn (fn acc hd) tl
    }
  }

val rec fold_right : ∀a b, (b ⇒ a ⇒ a) ⇒ list⟨b⟩ ⇒ a ⇒ a =
  fun fn l acc {
    case l {
      []       → acc
      hd :: tl → fn hd (fold_right fn tl acc)
    }
  }

val sum : list⟨nat⟩ ⇒ nat = (fold_left add zero)

infix (@) = app priority 3 left associative

val rec (@) : ∀b, list⟨b⟩ ⇒ list⟨b⟩ ⇒ list⟨b⟩ =
  fun l1 l2 {
    case l1 {
      []       → l2
      hd :: tl → hd :: (tl @ l2)
    }
  }

val rec rev_app : ∀b, list⟨b⟩ ⇒ list⟨b⟩ ⇒ list⟨b⟩ =
  fun l1 l2 {
    case l1 {
      []       → l2
      hd :: tl → rev_app tl (hd :: l2)
    }
  }

val rev : ∀b, list⟨b⟩ ⇒ list⟨b⟩ = fun l { rev_app l [] }

val print_list : ∀a, (a → {}) ⇒ list⟨a⟩ → {} =
  fun print_elt l {
    print "[";
    iter2 (fun e { print_elt e; print ";" }) l;
    print "]"
  }

val println_list : ∀a, (a → {}) ⇒ list⟨a⟩ → {} =
  fun print_elt l {
    print_list print_elt l;
    print "\n"
  }
