Require Import Arith.

Fixpoint sum_odd(n:nat) : nat :=
  match n with
  | O => O
  | S m => 1 + m + m + sum_odd m
  end.

Goal forall n, sum_odd n = n * n.
Proof.
  intros.
  induction n.
    reflexivity.

    simpl.
    rewrite IHn.
    rewrite mult_succ_r.
    rewrite (plus_comm (n * n) n).
    rewrite plus_assoc.
    reflexivity.
Qed.
