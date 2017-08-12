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

// Stream of the natural numbers.
//val rec naturals : stream<nat> = fun _ →
//  {hd = Z; tl = map (fun n → S[n]) naturals}
// FIXME needs size preserving map function
