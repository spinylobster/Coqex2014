Inductive pos : Set :=
  | SO : pos
  | S : pos -> pos.

Fixpoint plus(n m:pos) : pos := 
  match n with
  | SO => m
  | S n' => plus n' m
  end.

Infix "+" := plus.

Theorem plus_assoc : forall n m p, n + (m + p) = (n + m) + p.
Proof.
  intros.
  induction n.
    reflexivity.
    simpl; assumption.
Qed.
