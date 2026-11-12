(* Existing imports keep working after the repository split. *)
From SMTCoq Require Import SMTCoq.
From Stdlib Require Import ZArith.
Local Open Scope Z_scope.

Lemma compatibility_fast_lia : forall x y : Z,
  x <= y -> y < x + 1 -> x = y.
Proof. smtrocq. Qed.
Print Assumptions compatibility_fast_lia.

Lemma compatibility_strict_uf : forall (f : Z -> Z) (x y : Z),
  x = y -> f x = f y.
Proof. cvc5_eunoia. Qed.
Print Assumptions compatibility_strict_uf.

Example compatibility_false_goals : True.
Proof.
  Fail assert (forall x : Z, x < x) by smtrocq.
  Fail assert (forall x : Z, x = x + 1) by cvc5_eunoia.
  exact I.
Qed.
Print Assumptions compatibility_false_goals.
