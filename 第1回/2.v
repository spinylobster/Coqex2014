Theorem Modus_tollens : forall P Q : Prop, ~Q /\ (P -> Q) -> ~P.
Proof.
  intros.
  intro.
  destruct H.
  apply H.
  apply (H1 H0).
Qed.
