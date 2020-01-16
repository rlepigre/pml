include lib.stream
include lib.list
include lib.nat

val rec print_nat_list : list⟨nat⟩ ⇒ {} =
  fun l {
    case l {
      Nil     → print "\n"
      Cons[c] → print_nat c.hd; print " "; print_nat_list c.tl
    }
  }

val test0 : {} = print_nat_list (takes 0 naturals)
val test1 : {} = print_nat_list (takes 1 naturals)
val test2 : {} = print_nat_list (takes 2 naturals)
val test3 : {} = print_nat_list (takes 3 naturals)
val test4 : {} = print_nat_list (takes 4 naturals)
val test5 : {} = print_nat_list (takes 5 naturals)

// Stream of the natural numbers.
val naturals : stream⟨nat⟩ =
  let rec aux : nat ⇒ stream⟨nat⟩ =
    fun i { lazy { {hd = i; tl = aux S[i]} } };
  aux Zero

// Map function.
val rec map : ∀o, ∀a b, (a ⇒ b) ⇒ stream^o⟨a⟩ ⇒ stream^o⟨b⟩ =
  fun f s { lazy {
    let c = force s;
    {hd = f c.hd ; tl = map f c.tl}
  } }


val cons : ∀o, ∀a, a ⇒ stream^o⟨a⟩ ⇒ stream^(o+ₒ1)⟨a⟩ =
  fun a s { lazy {
    { hd = a; tl = s }
  } }

// Map function.
//val rec map : ∀o, ∀a b, (a ⇒ b) ⇒ sstream⟨o,a⟩ ⇒ sstream⟨o,b⟩ =
//  fun f s {
//    let c = s {};
//    cons (f c.hd) (map f c.tl)
//  }
////Does not work, we do not know that o ⟩ 0 when computing s {}

// val rec map : ∀a b, (a ⇒ b) ⇒ stream⟨a⟩ ⇒ stream⟨b⟩ =
//   fun f s {
//     let c = s {};
//     cons (f c.hd) (map f c.tl)
//   }
// // idem, but loose termination only because positivity is not there when
// // type the recursive call

// Stream of the natural numbers.
val rec naturals : stream⟨nat⟩ =
  lazy {
    {hd = Zero; tl = map succ naturals}
  }
