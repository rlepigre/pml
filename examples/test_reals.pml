include lib.nat
include lib.int
include lib.stream
include examples.reals

// Tests for reals

val r0   : real = { exp = 0; man = man0 }
val r1   : real = { exp = 1; man = cons S man0 }
val rn1  : real = { exp = 1; man = cons P man0 }

val half : real = { exp = 0; man = cons S man0 }
val rec man3 : man = fun _ { { hd = S; tl = fun _ { { hd = P; tl = man3 }}}}
val third : real = { exp = 0; man = man3 }

val size : nat = 3

val ones : bds⟨2⟩ = repeat (p1 : bint⟨p2⟩)
val test : {} = print_man size (divideBy 2 ones); print " = 1000000000\n"
val ones : bds⟨3⟩ = repeat (p1 : bint⟨p3⟩)
val test : {} = print_man size (divideBy 3 ones);
  print " = 1(-1)1(-1)1(-1)1(-1)1(-1)\n"
val twos : bds⟨3⟩ = repeat (p2 : bint⟨p3⟩)
val test : {} = print_man size (divideBy 3 twos); print " = 1010101010\n"

val test : {} = print_man size (opp_man man3);
  print " = (-1)1(-1)1(-1)1(-1)1(-1)1\n"
val test : {} = print_man size (average man3 (opp_man man3));
  print " = 0000000000\n"
val x31 : man = mul_man man3 man1
val x13 : man = mul_man man1 man3
val test : {} = print_man size x31; print " = 1(-1)1(-1)1(-1)1(-1)1(-1)\n"
val test : {} = print_man size x13; print " = 1(-1)1(-1)1(-1)1(-1)1(-1)\n"
val test : {} = print_man size (average x31 (opp_man x13));
  print " = 0000000000\n"
val test : {} = print_real size third;
  print " = 1(-1)1(-1)1(-1)1(-1)1(-1)E0\n"
val test : {} = print_real size (add half third); print " = 1/2 + 1/3\n"
val test : {} = print_real size (add third half); print " = 1/3 + 1/2\n"
val test : {} = print_real size (add third third); print " = 1/3 + 1/3\n"
val test : {} = print_real size (mul half third); print " = 1/2 * 1/3\n"
val test : {} = print_real size (mul third half); print " = 1/3 * 1/2\n"
val test : {} = print_real size (mul third third); print " = 1/3 * 1/3\n"
val test : {} = print_man size (i2 man0); print " = 1 / (2 - 0)\n"
val test : {} = print_man size (i2 man1); print " = 1 / (2 - 1)\n"
val test : {} = print_man size (i2 mann1); print " = 1 / (2 + 1)\n"
val test : {} = print_real size (inv half (1, {})); print " = inv (1 / 2)\n"
val i3 : real = inv third (2, {})
val test : {} = print_real size i3; print " = inv (1 / 3)\n"
val test : {} = print_real size (mul third i3); print " = 1\n"
