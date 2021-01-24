(* 元論文 https://www2.math.su.se/reports/2001/11/ *)
(* 元記事 https://qiita.com/lotz/items/60c20189f931dd8e5e9f *)

(* 
 * Ring の構造を真似て作る ?
 * https://coq.inria.fr/distrib/8.5beta3/stdlib/Coq.setoid_ring.Ring.html#
 * https://coq.inria.fr/distrib/8.5beta3/stdlib/Coq.setoid_ring.Ring_theory.html# 
 *)

(* 可換モノイド https://github.com/palmskog/monoid-ssreflect *)

(* 
 * 型クラスによる表現 https://m-hiyama.hatenablog.com/entry/20150124/1422063926
 * アンバンドル方式での半環 https://m-hiyama.hatenablog.com/entry/20150125/1422174390
 *)

From mathcomp Require Import ssreflect ssrnat.

Section Wheel.

Class BinOp (H: Set) := bin_op : H -> H -> H.

Definition Associative {H: Set} (op: BinOp H) :=
  forall(x y z: H), op x (op y z) = op (op x y) z.

Definition UnitLeft {H: Set} (op: BinOp H) (u: H) :=
  forall(x: H), op u x = x.

Definition UnitRight {H: Set} (op: BinOp H) (u: H) :=
  forall(x: H), op x u  = x.

Definition Commutative {H: Set} (op: BinOp H) :=
  forall(x y: H), op x y = op y x.

Definition Inv (H: Set) := H -> H.

Definition Involutive {H: Set} (f: Inv H) :=
  forall(x: H), f (f x) = x.

Definition AntiInvolutive {H: Set} (f: Inv H) (op: BinOp H) :=
  forall(x y: H), f (op x y) = op (f y) (f x).

Class CommutativeMonoid {H: Set} (unit: H) (op: BinOp H) := {
  assoc: Associative op;
  unit_l: UnitLeft op unit;
  unit_r: UnitRight op unit;
  comm: Commutative op
}.

Class CommutativeInvolutionMonoid {H: Set} (unit: H) (op: BinOp H) (inv: Inv H) := {
  commutative_monoid :> CommutativeMonoid unit op;

  involution: Involutive inv;
  anti_involution: AntiInvolutive inv op
}.

Class Add (H: Set) := add_op :> BinOp H.
Class Mul (H: Set) := mul_op :> BinOp H.

(* クラス定義中の中置演算子使用 https://stackoverflow.com/questions/48394056/using-implicit-type-class-parameters-in-coq-notation *)
(* 前置演算子を扱う方法はちょっとわからない *)

Delimit Scope wheel_scope with wheel.
Infix "+" := add_op: wheel_scope.
Infix "*" := mul_op: wheel_scope.

Open Scope wheel_scope.

Class Wheel {H: Set} (zero: H) (one: H) (add: Add H) (mul: Mul H) (inv: Inv H) := {
  wheel_add__commutative_monoid :> CommutativeMonoid zero add; (* 1 *)
  wheel_mul_commutative_involution_monoid :> CommutativeInvolutionMonoid one mul inv; (* 2 *)

  (* Distributivity *)
  wheel_distrib_l: forall(x y z: H), (x + y) * z + zero * z = x * z + y * z; (* 3 *)
  wheel_distrib_4: forall(x y z: H), x * inv y + z + zero * y = (x + y * z) * inv y; (* 4 *)

  (* Rules for zero-terms *)
  wheel_zero_idemponent: zero * zero = zero; (* 5 *)
  wheel_zero_6: forall(x y z: H), (x + zero * y) * z = x * z + zero * y; (* 6 *)
  wheel_zero_7: forall(x y: H), inv (x + zero * y) = inv x + zero * y; (* 7 *)
  wheel_zero_8: forall(x: H), x + zero * inv zero = zero * inv zero; (* 8 *)
}. 

(* 実装 *)

Inductive nat_w : Set :=
| W : nat -> nat -> nat_w.

Definition zero := W 0 1.
Definition one := W 1 1.
Definition add n m :=
  match n, m with
  | W x y, W x' y' => W (x * y' + x' * y) (y * y')
  end.
Definition mul n m :=
  match n, m with
  | W x y, W x' y' => W (x * x') (y * y')
  end.
Definition inv n :=
  match n with
  | W x y => W y x
  end.

(* 証明: 上記の台集合よおび演算の構成がWheelを成すことを示す *)

Delimit Scope nat_wheel_scope with wheel.
Infix "+" := add: nat_wheel_scope.
Infix "*" := mul: nat_wheel_scope.

Open Scope nat_wheel_scope.

Lemma natWheel_assoc_add : Associative add.
Proof.
  rewrite /Associative.
  intros x y z.
  case x => a b; case y => c d; case z => e f.
  rewrite /=.
  rewrite !mulnDl.
  rewrite !mulnA.
  rewrite !addnA.
  rewrite -!mulnA.
  rewrite (_ : muln f b = muln b f). (* 演算子を使うと nat_w のスコープなのでパタンマッチに失敗する *)
  rewrite (_ : muln d b = muln b d).
  by [].
  by rewrite mulnC.
  by rewrite mulnC.
Qed.

Lemma natWheel_unit_l_add_zero : UnitLeft add zero.
Proof.
  rewrite /UnitLeft.
  intros x.
  case x => a b.
  rewrite /zero.
  rewrite /=.
  by rewrite mul0n add0n muln1 mul1n.
Qed.

Lemma natWheel_unit_r_add_zero : UnitRight add zero.
Proof.
  rewrite /UnitRight.
  intros x.
  case x => a b.
  rewrite /zero.
  rewrite /=.
  by rewrite muln1 mul0n addn0 muln1.
Qed.

Lemma natWheel_comm_add : Commutative add.
Proof.
  rewrite /Commutative.
  intros x y.
  case x => a b; case y => c d.
  rewrite /=.
  rewrite addnC.
  rewrite (_ : muln b d = muln d b).
  by [].
  by rewrite mulnC.
Qed.

Theorem natWheel_1 : CommutativeMonoid zero add.
Proof.
  split.
  apply natWheel_assoc_add.
  apply natWheel_unit_l_add_zero.
  apply natWheel_unit_r_add_zero.
  apply natWheel_comm_add.
Qed.

Lemma natWheel_assoc_mul : Associative mul.
Proof.
  rewrite /Associative.
  intros x y z.
  case x => a b; case y => c d; case z => e f.
  rewrite /=.
  by rewrite !mulnA.
Qed.

Lemma natWheel_unit_l_mul_one : UnitLeft mul one.
Proof.
  rewrite /UnitLeft.
  intros x.
  case x => a b.
  rewrite /zero.
  rewrite /=.
  by rewrite !mul1n.
Qed.

Lemma natWheel_unit_r_mul_one : UnitRight mul one.
Proof.
  rewrite /UnitRight.
  intros x.
  case x => a b.
  rewrite /zero.
  rewrite /=.
  by rewrite !muln1.
Qed.

Lemma natWheel_comm_mul : Commutative mul.
Proof.
  rewrite /Commutative.
  intros x y.
  case x => a b; case y => c d.
  rewrite /=.
  rewrite (_ : muln a c = muln c a).
  rewrite (_ : muln b d = muln d b).
  by [].
  by rewrite mulnC.
  by rewrite mulnC.
Qed.

Lemma natWheel_inv : Involutive inv.
Proof.
  rewrite /Involutive.
  intro x.
  case x => a b.
  by rewrite /=.
Qed.

Lemma natWheel_anti_inv : AntiInvolutive inv mul.
Proof.
  rewrite /AntiInvolutive.
  intros x y.
  case x => a b; case y => c d.
  rewrite /=.
  rewrite (_ : muln a c = muln c a).
  rewrite (_ : muln b d = muln d b).
  by [].
  by rewrite mulnC.
  by rewrite mulnC.
Qed.

Theorem natWheel_2 : CommutativeInvolutionMonoid one mul inv.
Proof.
  split.
  split.
  apply natWheel_assoc_mul.
  apply natWheel_unit_l_mul_one.
  apply natWheel_unit_r_mul_one.
  apply natWheel_comm_mul.
  apply natWheel_inv.
  apply natWheel_anti_inv.
Qed.

Theorem natWheel_3 : forall x y z : nat_w, (x + y) * z + zero * z = x * z + y * z.
Proof.
Admitted.

Theorem natWheel_4 : forall x y z : nat_w, x * inv y + z + zero * y = (x + y * z) * inv y.
Proof.
Admitted.

Theorem natWheel_5 : zero * zero = zero.
Proof.
Admitted.

Theorem natWheel_6 : forall x y z : nat_w, (x + zero * y) * z = x * z + zero * y.
Proof.
Admitted.

Theorem natWheel_7 : forall x y : nat_w, inv (x + zero * y) = inv x + zero * y.
Proof.
Admitted.

Theorem natWheel_8 : forall x : nat_w, x + zero * inv zero = zero * inv zero.
Proof.
Admitted.

Instance natWheel : Wheel zero one add mul inv.
Proof.
  split.
  apply natWheel_1.
  apply natWheel_2.
  apply natWheel_3.
  apply natWheel_4.
  apply natWheel_5.
  apply natWheel_6.
  apply natWheel_7.
  apply natWheel_8.
Qed.


Definition fromNat n := W n 1.

(* Example example_1_2: forall(x y z: natWheel), ((x + 4 + 0 * y) * (2 + 0 * z) + (0 * x)) * (2 + 0 * z) = (x + 4) * 2 * 2 + 0 * x + 0 * y + 0 * z + 0 * z. *)

End Wheel.
