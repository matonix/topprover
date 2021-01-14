Require Import Problem Coq.Arith.Lt Coq.Arith.Gt.

Theorem solution: task.
Proof.
  unfold task.
  intros.
  induction n.
  induction m.
  - right. left. reflexivity.
  - left. apply lt_O_Sn.
  - destruct IHn.
    + induction m.
      * right. right. apply gt_Sn_O.
      * apply lt_n_Sm_le in H. apply le_lt_or_eq in H. {
        destruct H.
          - left. apply lt_n_S. assumption.
          - right. left. apply eq_S. assumption.
      }
    + destruct H.
      * right. right. rewrite H. apply gt_Sn_n.
      * right. right. assert (S n > n). { apply gt_Sn_n. } {
        apply gt_trans with (n := (S n)) (m := n) (p := m).
        - assumption.
        - assumption.  
      }
Qed.