Theorem DeMorgan1 : forall P Q : Prop, ~P \/ ~Q -> ~(P /\ Q).
Proof.
  unfold not.
  intros.
  destruct H.
  destruct H0.
  apply (H H0).
  destruct H0.
  apply (H H1).
Qed.

Theorem DeMorgan2 : forall P Q : Prop, ~P /\ ~Q -> ~(P \/ Q).
Proof.
  unfold not.
  intros.
  destruct H.
  destruct H0.
  apply (H H0).
  apply (H1 H0).
Qed.

Theorem DeMorgan3 : forall P Q : Prop, ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  unfold not.
  split.
  intro.
  apply H.
  apply (or_introl H0).
  intro.
  apply H.
  apply (or_intror H0).
Qed.

