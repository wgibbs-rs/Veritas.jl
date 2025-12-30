From Stdlib Require Import ZArith.
Open Scope Z_scope.

Definition double (x : Z) : Z :=
  x * 2.

Lemma double_post_condition_1 : forall x : Z, double x = x * 2.
Proof.
  intros x.
  reflexivity.
Qed.
