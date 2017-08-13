include lib.stream
include lib.nat
include lib.either

val rec is_odd : nat ⇒ bool = fun n →
  case n {
    Z[_] → false
    S[p] →
      case p {
        Z[_] → true
        S[p] → is_odd p
      }
  }

type odd  = {v∈nat | is_odd v ≡ true }
type even = {v∈nat | is_odd v ≡ false}

//val rec aux : (stream<even> ⇒ []) ⇒ (stream<odd> ⇒ []) ⇒ stream<nat> ⇒ [] =
//  fun fe fo s →
//    let hd = (s {}).hd in
//    let tl = (s {}).tl in
//    if is_odd hd {
//      let tl = save o → aux fe (fun x → restore o x) tl in
//      fo (fun _ → {hd = hd; tl = tl})
//    } else {
//      let tl = save e → aux (fun x → restore e x) fo tl in
//      fo (fun _ → {hd = hd; tl = tl})
//    }

//val itl : stream<nat> ⇒ either<stream<even>, stream<odd>> =
//  fun s → save a → InL[save e → restore a InR[save o →
//    aux (fun x → restore e x) (fun x → restore o x) s]]
