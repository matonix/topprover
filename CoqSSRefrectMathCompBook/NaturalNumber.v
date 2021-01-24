From mathcomp Require Import ssreflect ssrnat.

Section natrualNumber.
  
Lemma add0nEqn (n : nat) : 0 + n = n.
Proof.
  by [].
Qed.

Lemma addn3Eq2n1 (n : nat) : n + 3 = 2 + n + 1.
Proof.
  rewrite addn1.
  rewrite add2n.
  rewrite addnC.
  by [].
Qed.

Fixpoint sum n := if n is m.+1 then sum m + n else 0.
(* n is m.+1 のところはいわゆるパターンマッチ？ *)

Lemma sumGauss (n : nat) : sum n * 2 = (n + 1) * n.
Proof.
  (* move: n; elim.
  move => //.
  move =>  n.
  move => IHn. *)
  elim: n => [// | n IHn]. (* induction *)
  rewrite mulnC.
  rewrite (_ : sum (n.+1) = n.+1 + (sum n)); last first. (* replace *)
  rewrite /=. (* simpl. *)
  by rewrite addnC.
  rewrite mulnDr.
  rewrite mulnC in IHn. (* コンテキストへの適用 *)
  rewrite IHn.
  rewrite 2!addn1. (* 2回適用 *)
  rewrite [_ * n]mulnC. (* パターンマッチ適用 *)
  rewrite -mulnDl. (* 右辺から左辺への書き換え *)
  by [].
Qed.

End natrualNumber.
