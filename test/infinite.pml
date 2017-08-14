include lib.stream
include lib.nat
include lib.either

val rec is_odd : nat ⇒ bool =
  fun n {
    case n {
      Z    → false
      S[p] →
        case p {
          Z    → true
          S[p] → is_odd p
        }
    }
  }

val rec odd_total : ∀n∈nat, ∃v:ι, is_odd n ≡ v =
  fun n {
    case n {
      Z    → {}
      S[p] →
        case p {
          Z    → {}
          S[p] → odd_total p
        }
    }
  }

type bot = ∀x,x
val abort : ∀y, bot ⇒ y = fun x { x }

type odd  = {v∈nat | is_odd v ≡ true }
type even = {v∈nat | is_odd v ≡ false}

type sstream<o,a> = νo stream {} ⇒ {hd : a; tl : stream}
type csstream<o,a> = {hd : a; tl : sstream<o,a>}

val rec aux : ∀a b, (csstream<a,even> ⇒ bot) ⇒ (csstream<b,odd> ⇒ bot)
             ⇒ stream<nat> ⇒ bot =
  fun fe fo s {
    let hd = (s {}).hd in
    let tl = (s {}).tl in
    use { odd_total hd };
    if is_odd hd {
      fo {hd = hd; tl = fun _ { save o {
        abort (aux fe (fun x { restore o x }) tl) } }}
    } else {
      fe {hd = hd; tl = fun _ { save e {
        abort (aux (fun x { restore e x }) fo tl) } }}
    }
  }

val itl : stream<nat> ⇒ either<stream<even>, stream<odd>> =
  fun s {
    save a {
      InL[fun _ { save e { restore a InR[fun _ { save o {
        abort (aux (fun x { restore e x}) (fun x { restore o x }) s) } }] } }]
    }
  }

include test.stream_nat

val test : nat ⇒ {} =
  fun n {
    case itl naturals {
      InL[s] → let l = take n s in print "InL "; print_nat_list l
      InR[s] → let l = take n s in print "InR "; print_nat_list l
    }
  }

val test0 : {} = test Z
val test1 : {} = test S[Z]
val test2 : {} = test S[S[Z]]
val test3 : {} = test S[S[S[Z]]]
val test4 : {} = test S[S[S[S[Z]]]]
val test5 : {} = test S[S[S[S[S[Z]]]]]
val test6 : {} = test S[S[S[S[S[S[Z]]]]]]
