Require Import Coq.Arith.Arith.

Fixpoint u (m : nat) : nat :=
  match m with
  | 0    => 0
  | S m' => 2*m'+1 + u m'
  end.
Theorem odd_sum : forall n:nat, u n = n*n.
intro n.
  induction n.
  simpl.
  reflexivity.
simpl.
rewrite IHn.
ring.
Qed.
