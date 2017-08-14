include lib.stream
include lib.list
include lib.nat

val rec print_nat_list : list<nat> ⇒ {} = fun l →
  case l {
    Nil     → print "\n"
    Cons[c] → print_nat c.hd; print " "; print_nat_list c.tl
  }

val test0 : {} = print_nat_list (take Z                naturals)
val test1 : {} = print_nat_list (take S[Z]             naturals)
val test2 : {} = print_nat_list (take S[S[Z]]          naturals)
val test3 : {} = print_nat_list (take S[S[S[Z]]]       naturals)
val test4 : {} = print_nat_list (take S[S[S[S[Z]]]]    naturals)
val test5 : {} = print_nat_list (take S[S[S[S[S[Z]]]]] naturals)

// Stream of the natural numbers.
val naturals : stream<nat> =
  let rec aux : nat ⇒ stream<nat> =
    fun i _ → {hd = i; tl = aux S[i]}
  in aux Z

type sstream<o,a> = νo stream {} ⇒ {hd : a; tl : stream}

// Map function.
val rec map : ∀o, ∀a b, (a ⇒ b) ⇒ sstream<o,a> ⇒ sstream<o,b> = fun f s _ →
  let c = s {} in
  {hd = f c.hd ; tl = map f c.tl}


val cons : ∀o, ∀a, a ⇒ sstream<o+1,a> ⇒ sstream<o,a> =
  fun a s _ → { hd = a; tl = s }

// Map function.
//val rec map : ∀o, ∀a b, (a ⇒ b) ⇒ sstream<o,a> ⇒ sstream<o,b> = fun f s →
//  let c = s {} in
//  cons (f c.hd) (map f c.tl)
// Does not work, we do not know that o > 0 when computing s {}

//val rec map : ∀a b, (a ⇒ b) ⇒ stream<a> ⇒ stream<b> = fun f s →
//  let c = s {} in
//  cons (f c.hd) (map f c.tl)
// idem, but loose termination only because positivity is not there when
// type the recursive call

// Stream of the natural numbers.
val rec naturals : stream<nat> = fun _ →
  {hd = Z; tl = map succ naturals}
