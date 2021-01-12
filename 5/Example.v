Require Import Problem Coq.Arith.Mult Coq.Arith.Plus.

Theorem solution: task.
Proof.
  unfold task.
  intros.
  assert (S m = 1 + m).
  - reflexivity.
  - rewrite H. rewrite mult_plus_distr_l. rewrite mult_1_r. reflexivity.
Qed.

