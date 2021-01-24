Record magma : Type := Magma {
  carrier : Type;
  operator : carrier -> carrier -> carrier
}.

Check magma.

Check Magma.

Definition prop_and_magma := Magma Prop and.

Definition nat_plus_magma := Magma nat plus.

Print prop_and_magma.

Print nat_plus_magma.

Lemma PropMagmaFalse (x y : carrier prop_and_magma):
  operator prop_and_magma x False -> y.
Proof.
Abort.

Record semigroup : Type := Semigroup {
  scarrier : magma;
  assoc : forall a b c : carrier scarrier,
    operator scarrier a (operator scarrier b c)
    = operator scarrier (operator scarrier a b) c
}.

From mathcomp Require Import ssrnat.

Definition nat_plus_semigroup := Semigroup nat_plus_magma addnA.

Print addnA.

Check nat_plus_semigroup.


