Require Import Lists.List.

Fixpoint sum (xs: list nat) : nat :=
  match xs with
    | nil => 0
    | x :: xs => x + sum xs
  end.

Theorem Pigeon_Hole_Principle :
  forall (xs : list nat), length xs < sum xs -> (exists x, 1<x /\ In x xs).
Proof.
  intros.
  induction xs.
    simpl in H.
    apply False_ind, (Lt.lt_irrefl 0 H).

    assert ((exists x : nat, 1 < x /\ In x xs) -> forall n, exists x : nat, 1 < x /\ In x (n :: xs)).
      intros.
      destruct H0. destruct H0.
      exists x.
      split.
        assumption. assert (In x (n :: xs)) by (apply (in_cons n x xs H1)); assumption.

    induction a.
      simpl in H.
      assert (forall n m, S n < m -> n < m).
        intros.
        induction m.
          apply False_ind, (Lt.lt_n_0 (S n) H1).
          apply (Lt.lt_S n m (Lt.lt_S_n n m H1)).
      assert (exists x : nat, 1 < x /\ In x xs) by (apply (IHxs (H1 (length xs) (sum xs) H))).
      apply (H0 H2).

      induction a.
        simpl in H.
        apply (H0 (IHxs (Lt.lt_S_n (length xs) (sum xs) H))).

        exists (S (S a)).
        split.
          apply (Lt.lt_n_S 0 (S a)), (Lt.lt_0_Sn a).
          apply (in_eq).
Qed.
