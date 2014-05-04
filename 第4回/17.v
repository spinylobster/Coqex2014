Theorem hoge : forall P Q R : Prop, P \/ ~(Q \/ R) -> (P \/ ~Q) /\ (P \/ ~R).
Proof.
  refine (fun P Q R => _).
  refine (fun H => _).
  refine match H with | or_introl HP => _ | or_intror HnQR => _ end.
  - refine (conj _ _).
    + refine (or_introl _).
      refine HP.
    + refine (or_introl _).
      refine HP.
  - refine (conj _ _).
    + refine (or_intror _).
      refine (fun HQ => _).
      refine (HnQR _).
      refine (or_introl _).
      refine HQ.
    + refine (or_intror _).
      refine (fun HR => _).
      refine (HnQR _).
      refine (or_intror _).
      refine HR.
Qed.
