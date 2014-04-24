Require Import Arith.

Goal forall n m p q : nat, (n + m) + (p + q) = (n + p) + (m + q).
Proof.
  intros.
  rewrite plus_assoc.
  rewrite plus_assoc.
  rewrite <- (plus_assoc n m p).
  rewrite (plus_comm m p).
  rewrite plus_assoc.
  reflexivity.
Qed.

Goal forall n m : nat, (n + m) * (n + m) = n * n + m * m + 2 * n * m.
Proof.
  intros.
  replace ((n + m) * (n + m)) with (n * n + n * m + n * m + m * m).
  replace (2 * n * m) with (n * m + n * m).
  rewrite (NPeano.Nat.add_shuffle0 (n * n) (m * m) (n * m + n * m)).
  rewrite plus_assoc.
  reflexivity.

  (* 2 * n * m = n * m + n * m *)
  rewrite <- (mult_plus_distr_r n n m).
  replace (n + n) with (2 * n) by (simpl; rewrite plus_0_r; reflexivity).
  reflexivity.

  (* n * n + n * m + m * n + m * m = (n + m) * (n + m) *)
  rewrite mult_plus_distr_r.
  rewrite mult_plus_distr_l.
  rewrite mult_plus_distr_l.
  rewrite plus_assoc.
  rewrite (mult_comm m n).
  reflexivity.
Qed.
