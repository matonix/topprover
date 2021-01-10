Require Import Problem.

Theorem plus_assoc_proof: plus_assoc.
Proof.
  unfold plus_assoc.
  intros.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite <- IHn. reflexivity.
Qed.