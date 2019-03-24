include lib.nat
include lib.nat_proofs
include lib.list

// rose tree without an extra node needs type annotations.
type rec rose = list⟨rose⟩

val rec size : rose ⇒ nat =
  fun l {
    let o such that l : rose^(o+ₒ1);
    let fn : nat ⇒ rose^(o) ⇒ nat = fun acc e { acc + (size e) };
    fold_left fn 1 (l:list⟨rose^o⟩)
  }

val rec height : rose ⇒ nat =
  fun l {
    let o such that l : rose^(o+ₒ1);
    let fn : nat ⇒ rose^(o) ⇒ nat = fun acc e { max acc S[height e] };
    fold_left fn 0 (l:list⟨rose^o⟩)
  }

val rec theorem : ∀o, ∀r∈list⟨rose^o⟩, leq (height r) (size r) =
  fun l {
    case l {
      []    → qed
      x::l' →
        show leq (height l') (size l') using theorem l';
        show leq (height x) (size x) using theorem x;
        {- -}
    }
  }

// rose tree with an extra node does not need type annotation.
type rec rose = [Node of list⟨rose⟩]

val rec size : rose ⇒ nat =
  fun n {
    case n {
      Node[l] → fold_left (fun acc e { acc + (size e) }) 1 l
    }
  }

val rec height : rose ⇒ nat =
  fun n {
    case n {
      Node[l] → fold_left (fun acc e { max acc S[height e] }) 0 l
    }
  }

val rec theorem : ∀o, ∀r∈rose^o, leq (height r) (size r) =
  fun n {
    case n {
      Node[l] →
        case l {
          []    → qed
          x::l' →
            //show leq (height Node[l']) (size Node[l']) using theorem Node[l'];
            {- -}
        }
    }
  }
