Require Import Problem List.

Theorem solution: task.
Proof.
  unfold task.
  intros l.
  unfold not.
  intro H.
  symmetry in H.
  revert H.
  apply app_cons_not_nil.
Qed.