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

val total : ∀a b, ∀f∈a⇒b, ∀x∈a, ∃v:ι, v ∈ b | v ≡ f x =
  fun f x { let y = f x; y }

type bot = ∀x,x
val abort : ∀y, bot ⇒ y = fun x { x }

type odd  = {v∈nat | is_odd v ≡ true }
type even = {v∈nat | is_odd v ≡ false}

type sstream⟨o,a⟩ = ν_o stream, {} → {hd : a; tl : stream}
type csstream⟨o,a⟩ = {hd : a; tl : sstream⟨o,a⟩}
type stream⟨a⟩=sstream⟨∞,a⟩

val rec aux : ∀a b, (csstream⟨a,even⟩ → bot) ⇒ (csstream⟨b,odd⟩ → bot)
             ⇒ stream⟨nat⟩ → bot =
  fun fe fo s {
    let hd = (s {}).hd;
    let tl = (s {}).tl;
    if is_odd hd {
      fo {hd = hd; tl = fun _ { save o {
        abort (aux fe (fun x { restore o x }) tl) } }}
    } else {
      fe {hd = hd; tl = fun _ { save e {
        abort (aux (fun x { restore e x }) fo tl) } }}
    }
  }

val itl : stream⟨nat⟩ ⇒ either⟨stream⟨even⟩, stream⟨odd⟩⟩ =
  fun s {
    save a {
      InL[fun _ { save e { restore a InR[fun _ { save o {
        abort (aux (fun x { restore e x}) (fun x { restore o x }) s) } }] } }]
    }
  }

include tests.stream_nat

// Compute the list of the first n elements of a stream.
val rec takes : ∀a, nat ⇒ stream⟨a⟩ → list⟨a⟩ =
  fun n s {
    case n {
           | Zero → Nil
           | S[k] → let c = s {};
                    let tl = takes k c.tl;
                    Cons[{hd = c.hd; tl = tl}]
    }
  }

// take2 is rejected (and should be rejected, s is in the context and classical
// val take2 : ∀a, nat ⇒ stream⟨a⟩ ⇒ list⟨a⟩ = fun n s { delim { take n s } }

type istream⟨a⟩ = ν stream, {} ⇒ {hd : a; tl : stream}

// marche avec le sous typage stream intuitioniste ⟨ stream classique
val take2 : ∀a, nat ⇒ istream⟨a⟩ ⇒ list⟨a⟩ = fun n s { delim { takes n s } }

val test : nat ⇒ either⟨list⟨nat⟩,list⟨nat⟩⟩ =
  fun n {
    delim { case itl naturals {
      InL[s] → InL[takes n s]
      InR[s] → InR[takes n s]
    } }
  }

val print_test : nat → {} =
  fun n {
    case test n {
      InL[l] → print "InL "; print_nat_list l
      InR[l] → print "InR "; print_nat_list l
    }
  }

val test0 : {} = print_test 0
val test1 : {} = print_test 1
val test2 : {} = print_test 2
val test3 : {} = print_test 3
val test4 : {} = print_test 4
val test5 : {} = print_test 5
val test6 : {} = print_test 6
