include lib.list
include lib.nat
include lib.either

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

val rec odd_total : ∀n∈nat, ∃v:ι, is_odd n ≡ v =
  fun n {
    case n {
      Zero → {}
      S[p] →
        case p {
          Zero → {}
          S[p] → odd_total p
        }
    }
  }

type bot = ∀x,x
val abort : ∀y, bot ⇒ y = fun x { x }

type odd  = {v∈nat | is_odd v ≡ true }
type even = {v∈nat | is_odd v ≡ false}

type sstream<o,a> = ν_o stream, {} → {hd : a; tl : stream}
type csstream<o,a> = {hd : a; tl : sstream<o,a>}
type stream<a>=sstream<∞,a>

val rec aux : ∀a b, (csstream<a,even> → bot) ⇒ (csstream<b,odd> → bot)
             ⇒ stream<nat> → bot =
  fun fe fo s {
    let hd = (s {}).hd;
    let tl = (s {}).tl;
    use odd_total hd;
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

// Compute the list of the first n elements of a stream.
val rec take : ∀a, nat ⇒ stream<a> → list<a> =
  fun n s {
    case n {
           | Z    → Nil
           | S[k] → let c = s {};
                    let tl = take k c.tl;
                    Cons[{hd = c.hd; tl = tl}]
    }
  }

val test : nat → {} =
  fun n {
    case itl naturals {
      InL[s] → let l = take n s; print "InL "; print_nat_list l
      InR[s] → let l = take n s; print "InR "; print_nat_list l
    }
  }

val test0 : {} = test u0
val test1 : {} = test u1
val test2 : {} = test u2
val test3 : {} = test u3
val test4 : {} = test u4
val test5 : {} = test u5
val test6 : {} = test u6
