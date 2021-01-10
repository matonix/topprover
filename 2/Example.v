Require Import Problem.

Lemma plus_n_0: forall n, n + 0 = n.
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite -> IHn. reflexivity.
Qed.

Lemma plus_n_Sm: forall n m, n + S m = S (n + m).
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl. rewrite -> IHn. reflexivity.
Qed. 

Theorem plus_comm_proof: plus_comm.
Proof.
  unfold plus_comm.
  intros.
  induction n.
  - rewrite -> plus_n_0. reflexivity.
  - simpl. rewrite -> plus_n_Sm. rewrite -> IHn. reflexivity.
Qed.
