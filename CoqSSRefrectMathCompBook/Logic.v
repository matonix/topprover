From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Logic.
  
Lemma contrap : forall A B : Prop, (A -> B) -> ~B -> ~A.
Proof.
  rewrite /not. (* unfold *)
  move => A0 B0 AtoB notB.
  by move /AtoB. (* transform to necessary condition *)
Qed.

Variables A B C : Prop.

(* 同値性に関する補題： 解釈補題 *)
Lemma AndOrDistL : (A /\ C) \/ (B /\ C) <-> (A \/ B) /\ C.
Proof.
  rewrite /iff.
  apply: conj. (* rewrite との違いは、 apply は関数の形式を持ってる場合に必要条件から十分条件に分解できるところ *)
  -case. (* or の帰納的な定義 or_introl, or_intror をそれぞれ適用したサブゴールを作る *)
    +case=> AisTrue CisTrue. (* case. move => ... の略記 *) 
     (* apply: conj.
      *by apply: or_introl.
      *by []. *)
      by apply: conj; [apply: or_introl | ].
    +case=> BisTrue CisTrue.
      by apply: conj; [apply: or_intror | ].
  -case=> AorBisTrue CisTrue.
   case: AorBisTrue => [AisTrue | BisTrue].
    +by apply: or_introl.
    +by apply: or_intror.
Qed.

Lemma JDM (T : Type) (P : T -> Prop): ~(exists (x : T), P x) <-> forall x, ~(P x).
Proof.
  (* rewrite /iff. *) (* 省略可 *)
  apply: conj => Hyp.
  -move=> x0 HPx0.
   apply: Hyp.
   by apply: (ex_intro P x0).
  -by case.
Qed.

(* 直観論理には存在しない排中律 Law of excluded middle の導入 *)
Hypothesis ExMidLaw : forall P : Prop, P \/ ~P.

Lemma notnotEq (P : Prop): ~ ~ P -> P.
Proof.
  move => notnotP.
  -case: (ExMidLaw (~ P)).
   +by move /notnotP. (* わからん *)
   +by case: (ExMidLaw P).  (* わからん *)
Qed.

End Logic.