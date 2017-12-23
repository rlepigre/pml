include lib.nat
include lib.list

// FIXME should work ?
//type rec rose<a> = list<rose>
//
//val rec size : ∀a, rose<a> ⇒ nat =
//  fun l {
//    fold_left (fun acc e { acc + (size e) }) 0 l
//  }

type rec rose<a> = [Node of list<rose>]

val rec size : ∀a, rose<a> ⇒ nat =
  fun n {
    case n {
      Node[l] → fold_left (fun acc e { S[acc] + (size e) }) 0 l
    }
  }

val rec height : ∀a, rose<a> ⇒ nat =
  fun n {
    case n {
      Node[l] → fold_left (fun acc e { max acc S[height e] }) 0 l
    }
  }

val rec theorem : ∀a, ∀r∈rose<a>, leq (height r) (size r) =
  fun n {
    case n {
      Node[l] →
        case l {
          []    → qed
          x::l' →
            //show leq (height Node[l]) (size Node[l]) using theorem Node[l];
            {- TODO -}
        }
    }
  }
