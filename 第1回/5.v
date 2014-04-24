Theorem NotNot_LEM : forall P : Prop, ~ ~(P \/ ~P).
Proof.
  unfold not.
  intros.
  apply H.
  right.
  intro.
  apply (H (or_introl H0)).
Qed.

