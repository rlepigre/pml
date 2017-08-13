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

val rec odd_total : ∀n∈nat, ∃v:ι, is_odd n ≡ v = fun n →
  case n {
    Z    → {}
    S[p] →
      case p {
        Z    → {}
        S[p] → odd_total p
      }
  }

type bot = ∀x,x
val abort : ∀y, bot ⇒ y = fun x → x

type odd  = {v∈nat | is_odd v ≡ true }
type even = {v∈nat | is_odd v ≡ false}

type sstream<o,a> = νo stream {} ⇒ {hd : a; tl : stream}
type csstream<o,a> = {hd : a; tl : sstream<o,a>}

//val rec aux : ∀a b, (csstream<a,even> ⇒ bot) ⇒ (csstream<b,odd> ⇒ bot)
//              ⇒ stream<nat> ⇒ bot =
//  fun fe fo s →
//    let hd = (s {}).hd in
//    let tl = (s {}).tl in
//    use odd_total hd;
//    if is_odd hd {
//      let tl = fun _ → save o → abort (aux fe (fun x → restore o x) tl) in
//      fo {hd = hd; tl = tl}
//    } else {
//      let tl = fun _ → save e → abort (aux (fun x → restore e x) fo tl) in
//      fe {hd = hd; tl = tl}
//    }

//val itl : stream<nat> ⇒ either<stream<even>, stream<odd>> =
//  fun s → save a → InL[save e → restore a InR[save o →
//    aux (fun x → restore e x) (fun x → restore o x) s]]
