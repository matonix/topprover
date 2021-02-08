Require Import Problem Arith.
From mathcomp Require Import ssreflect.

Lemma L0: forall n m, product_of_range n (S m) = (S n) * product_of_range (S n) m.
Proof.
  by rewrite /=.
Qed.

Lemma L1: forall n m, product_of_range n (S m) = (n + S m) * product_of_range n m.
Proof.
  intros n m.
  revert n.
  elim: m => [| m' IHm'].
  intros n.
  by rewrite /= !Nat.mul_1_r Nat.add_1_r.
  intros.
  rewrite L0.
  rewrite IHm'.
  rewrite L0.
  by ring.
Qed.

Theorem solution: task.
Proof.
  rewrite /task.
  intros n m.
  revert n.
  elim m => [| m' IHm].
  rewrite /product_of_range. 
  exists 1. 
  by rewrite /=.
  intros n.
  elim n => [| n' IHn].
  exists 1.
  by rewrite /=.
  case: (IHm (S n')) => p Hp.
  case: IHn => k Hk.
  exists (p + k).
  rewrite L1.
  rewrite L0 in Hk.
  repeat rewrite Nat.mul_add_distr_r.
  rewrite Hk.
  rewrite Hp.
  rewrite (_ : S m' * (p * product_of_range 0 m') = p * ((0 + S m') * product_of_range 0 m')).
  rewrite -L1.
  by rewrite Nat.add_comm.
  rewrite Nat.add_0_l.
  rewrite !Nat.mul_assoc.
  by rewrite (Nat.mul_comm (S m') p).
Qed.