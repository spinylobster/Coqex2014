Definition tautology : forall P : Prop, P -> P
  := fun P p => p.

Definition Modus_tollens : forall P Q : Prop, ~Q /\ (P -> Q) -> ~P
  := fun P Q H p => let (nQ, p_q) := H in nQ (p_q p).
 
Definition Disjunctive_syllogism : forall P Q : Prop, (P \/ Q) -> ~P -> Q
  := fun P Q p_or_q n_p =>
  match p_or_q with
  | or_introl p => False_ind Q (n_p p)
  | or_intror q => q
  end.

Definition tautology_on_Set : forall A : Set, A -> A
  := fun A p => p.

Definition Modus_tollens_on_Set : forall A B : Set, (B -> Empty_set) * (A -> B) -> (A -> Empty_set)
  := fun A B H a => let (b_emp, a_b) := H in b_emp (a_b a).

Definition Disjunctive_syllogism_on_Set : forall A B : Set, (A + B) -> (A -> Empty_set) -> B
  := fun A B in_a_b a_emp =>
  match in_a_b with
  | inl a => Empty_set_rec (fun _ : Empty_set => B) (a_emp a)
  | inr b => b
  end.

