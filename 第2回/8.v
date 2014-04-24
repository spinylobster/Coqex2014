Require Import Arith.

Goal forall m n : nat, (n * 10) + m = (10 * n) + m.
Proof.
  intros.
  rewrite mult_comm.
  reflexivity.
Qed.
