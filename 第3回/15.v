Inductive Tree:Set :=
  | Node: list Tree -> Tree.

Definition tail : forall (A : Type), list A -> list A
  := fun (A : Type) (l : list A) =>
  match l with
  | nil => nil
  | cons x l' => l'
  end.

Definition head : forall (A : Type), A -> list A -> A
  := fun (A : Type) (x : A) (l : list A) =>
  match l with
  | nil => x
  | cons a _ => a
  end.

Definition getNode : Tree -> list Tree
  := fun t => let (l) := t in l.

Lemma list_Tree_eq_LEM : forall l l',
  {Node l = Node l'} + {Node l <> Node l'} -> {l = l'} + {l <> l'}.
Proof.
  intros.
  destruct H.
  - left; exact (f_equal getNode e).
  - right; intro.
  apply n, (f_equal Node H).
Qed.

Theorem Tree_dec: forall a b:Tree, {a=b} + {a<>b}.
Proof.
  fix 1.
  destruct a; destruct b.
  generalize l l0; clear l; clear l0.
  induction l; induction l0.
  - left; reflexivity.
  - right; discriminate.
  - right; discriminate.
  - destruct (Tree_dec a a0).
    destruct (list_Tree_eq_LEM l l0 (IHl l0)).
    * left; subst; reflexivity.
    * right; subst.
    intro.
    assert (l = l0) by (apply (f_equal (tail Tree) (f_equal getNode H))).
    congruence.
    * right.
    intro.
    assert (a = a0) by (apply (f_equal (head Tree a) (f_equal getNode H))).
    congruence.
Qed.
