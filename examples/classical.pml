include lib.bool
include lib.nat

// Is a natural number even or odd?

val rec is_odd : nat ⇒ bool =
  fun n {
    case n {
      Zero → false
      S[p] →
        case p {
          Zero → true
          S[p] → is_odd p
        }
    }
  }

val is_even : nat ⇒ bool =
  fun n { not (is_odd n) }

// Type of odd / even numbers.

type odd  = {n∈nat | is_odd  n}
type even = {n∈nat | is_even n}

include lib.either
include lib.list

type neg⟨a⟩ = a → ∀x,x

type corec stream⟨a⟩ = {} → {hd : a; tl : stream}

// Stream cell of size [s].
type c⟨s,a⟩ = {hd : a; tl : stream^s⟨a⟩}

val rec aux : ∀se so, neg⟨c⟨se,even⟩⟩ ⇒ neg⟨c⟨so,odd⟩⟩ ⇒ neg⟨stream⟨nat⟩⟩ =
  fun fe fo s {
    let {hd; tl} = s {};
    if is_odd hd {
      fo {hd; tl = fun _ {save o {aux fe (fun x {restore o x}) tl}}}
    } else {
      fe {hd; tl = fun _ {save e {aux (fun x {restore e x}) fo tl}}}
    }
  }

val itl : stream⟨nat⟩ ⇒ either⟨stream⟨even⟩, stream⟨odd⟩⟩ =
  fun s {
    save a {
      InL[fun _ {
        save e {restore a InR[fun _ {
          save o {
            aux (fun x {restore e x}) (fun x {restore o x}) s
          }}]
        }}]
    }
  }
