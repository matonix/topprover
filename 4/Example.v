Require Import Problem.

(* Hint *)
Lemma lemma: forall (f: bool -> bool) b x y z,
    x = f b -> y = f x -> z = f y -> z = x.
Proof.
  intros. 
  rewrite -> H1.
  rewrite -> H0.
  rewrite -> H.
  induction b.
  - induction x.
    + rewrite <- H. rewrite <- H. rewrite <- H. reflexivity.
    + rewrite <- H. induction y.
      * rewrite <- H0. rewrite <- H. reflexivity.
      * rewrite <- H0. rewrite <- H0. reflexivity.
  - induction x.
    + rewrite <- H. induction y.
      * rewrite <- H0. rewrite <- H0. reflexivity.
      * rewrite <- H0. rewrite <- H. reflexivity.
    + rewrite <- H. rewrite <- H. rewrite <- H. reflexivity.
Qed.

Theorem solution: task.
Proof. unfold task. intros. eapply lemma; reflexivity. Qed.