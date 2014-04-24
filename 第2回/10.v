Parameter G : Set.
Parameter mult : G -> G -> G.
Notation "x * y" := (mult x y).
Parameter one : G.
Notation "1" := one.
Parameter inv : G -> G.
Notation "/ x" := (inv x).
(* Notation "x / y" := (mult x (inv y)). *) (* 使ってもよい *)

Axiom mult_assoc : forall x y z, x * (y * z) = (x * y) * z.
Axiom one_unit_l : forall x, 1 * x = x.
Axiom inv_l : forall x, /x * x = 1.

(* 解けなかったので@blackenedgoldさんの解答を借りました。 *)
Lemma inv_r : forall x, x * / x = 1.
Proof.
  intros.
  assert (x = / / x * 1).
    rewrite <- (inv_l x).
    rewrite mult_assoc.
    rewrite inv_l.
    rewrite one_unit_l.
    reflexivity.
  replace (x * / x) with (/ / x * 1 * / x) by (rewrite <- H; reflexivity).
  rewrite <- mult_assoc.
  rewrite one_unit_l.
  rewrite inv_l.
  reflexivity.
Qed.

Lemma one_unit_r : forall x, x * 1 = x.
Proof.
  intros.
  rewrite <- (inv_l x).
  rewrite mult_assoc.
  rewrite inv_r.
  rewrite one_unit_l.
  reflexivity.
Qed.