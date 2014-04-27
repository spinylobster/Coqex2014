Theorem FF: ~exists f, forall n, f (f n) = S n.
Proof.
  intro.
  destruct H.
  remember x as f; symmetry in Heqf; subst.

  assert (forall n, f (S n) = S (f n)).
    intro; rewrite <- H; rewrite <- H; reflexivity.
  assert (forall n, f n <> n).
    intro. intro.
    assert (f (f n) = S n) by (apply (H n)).
    rewrite H1 in H2; rewrite H1 in H2.
    apply (n_Sn n H2).
  assert (forall n, f n <> 0).
    intro.
    induction n.
      apply (H1 0).
      rewrite H0.
      intro.
      symmetry in H2.
      apply (O_S (f n) H2).
  assert (exists n, f 0 = n) by (exists (f 0); reflexivity).
  assert (forall n, f 0 <> n).
    intro.
    induction n.
      apply (H1 0).

      intro.
      assert (f (f 0) = f (S n)) by (apply (f_equal f H4)).
      rewrite H0 in H5.
      rewrite H in H5.
      assert (f n = 0) by (symmetry; apply (eq_add_S 0 (f n) H5)).
      apply (H2 n H6).

  destruct H3.
  apply (H4 x H3).
Qed.
