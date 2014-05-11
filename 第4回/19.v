Parameter A : Set.
Definition Eq : A -> A -> Prop :=
  fun a => fun b => forall P : A -> Prop, P a <-> P b.

Lemma Eq_eq : forall x y, Eq x y <-> x = y.
Proof.
  unfold Eq.
  intros x y; split.
    - intro E.
    destruct (E (fun z => x = z)).
    apply (H (eq_refl x)).
    - intro E.
    subst; split; auto.
Qed.