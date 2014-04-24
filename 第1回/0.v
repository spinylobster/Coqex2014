Theorem tautology : forall P : Prop, P -> P.
Proof.
  intros P H.
  assumption.
Qed.

(* Error: Attempt to save an incomplete proof *)
(*
Theorem wrong : forall P : Prop, P.
Proof.
  intros P.
Qed.
*)
