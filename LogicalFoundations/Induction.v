From LF Require Export Basics.

Theorem plus_n_O_firsttry : forall n:nat,
  n = n + 0.
Proof.
  intros.
  simpl.
Abort.

Theorem plus_n_0_secondtry: forall n:nat,
  n = n + 0.
Proof.
  intros n.
  destruct n as [| n'] eqn:E.
  - reflexivity.
  - simpl.
Abort.

Theorem plus_n_O : forall n:nat,
  n = n + 0.
Proof.
  intros n.
  induction n as [| n' IHn']. (* Induction Hypothesis *)
  - reflexivity.
  - simpl. 
    rewrite <- IHn'.
    reflexivity.
Qed.

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  induction n.
  - reflexivity.
  - simpl.
    rewrite -> IHn.
    reflexivity.
Qed.

(* practice ** basic induction *)

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite -> IHn. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite -> IHn. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros.
  induction n.
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite -> IHn. rewrite -> plus_n_Sm. reflexivity.
Qed.

(* 
  定理： 任意の自然数 n, m について、以下が成立する。
    n + m = m + n
  証明： n に関する帰納法による。
  - n = 0 の場合は、示す命題は、
      0 + m = m + 0
    である。 これは + の定義と、 m + 0 = m の定理から明らかである。
  - n = S n' の場合は、示す命題は、
      S n' + m = m + S n'
    である。 + の定義より、両辺は次の形に変形される。
      S (n' + m) = m + S n'
    帰納法の仮定 n' + m = m + n' を用いると、
      S (m + n') = m + S n'
    の形に変形される。これは、 S (n + m) = n + (S m) の定理から明らかである。
  証明終了。


*)

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite <- IHn. reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | 0 => 0
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n.
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite -> IHn. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros.
  rewrite -> plus_comm.
Abort.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n). { rewrite -> plus_comm. reflexivity. }
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros.
  rewrite -> plus_assoc.
  rewrite -> plus_assoc.
  assert (H2: n + m = m + n). { rewrite -> plus_comm. reflexivity. }
  rewrite -> H2.
  reflexivity.
Qed.

Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros.
  rewrite -> plus_assoc.
  rewrite -> plus_assoc.
  replace (n + m) with (m + n).
  - reflexivity.
  - rewrite -> plus_comm. reflexivity.
Qed.

Theorem bin_to_nat_pres_incr: forall n : bin,
  S (bin_to_nat n) = bin_to_nat (incr n).
Proof.
  intros.
  induction n.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl.
    rewrite <- IHn.
    simpl.
    rewrite -> plus_n_Sm.
    reflexivity.
Qed.

Fixpoint nat_to_bin (n:nat) : bin :=
  match n with
  | O => Z
  | S n' => incr (nat_to_bin n')
  end.

Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite <- bin_to_nat_pres_incr. rewrite -> IHn. reflexivity.
Qed.


  