//simple file to reproduce issue #24

include lib.nat

val wrong : ∀n∈nat, S[n] ≡ n = fun n {
  {--}
}

val loop : ∀n∈nat, {} = fun n {
  use wrong n;
  ✂
}