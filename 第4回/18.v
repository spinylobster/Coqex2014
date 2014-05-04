Require Import Arith.

Definition Nat : Type :=
  forall A : Type, (A -> A) -> (A -> A).

Definition NatPlus(n m : Nat) : Nat :=
  fun A f x => n A f (m A f x).

Definition nat2Nat : nat -> Nat := nat_iter.

Definition Nat2nat(n : Nat) : nat := n _ S O.

Lemma NatPlus_plus :
  forall n m, Nat2nat (NatPlus (nat2Nat n) (nat2Nat m)) = n + m.
Proof.
  assert (forall n m : nat, nat_iter n S m = n + m).
    intros.
    induction n.
    - reflexivity.
    - simpl; apply eq_S; assumption.
  - intros.
  unfold nat2Nat; unfold Nat2nat; unfold NatPlus.
  repeat rewrite H.
  rewrite plus_0_r.
  reflexivity.
Qed.
