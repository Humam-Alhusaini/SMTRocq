(* Live integer cuts using CVC5's raw rational/cast intermediates. *)
From SMTCoq Require Import SMTCoq.
From Stdlib Require Import Bool ZArith.
Local Open Scope Z_scope.

Lemma eunoia_integer_parity : forall x : Z, 2*x <> 1.
Proof. cvc5_eunoia. Qed.
Print Assumptions eunoia_integer_parity.

Lemma eunoia_integer_negative_parity : forall x : Z, 2*x <> -1.
Proof. cvc5_eunoia. Qed.
Print Assumptions eunoia_integer_negative_parity.

Lemma eunoia_integer_two_variable_parity : forall x y : Z, 2*x+4*y <> 1.
Proof. cvc5_eunoia. Qed.
Print Assumptions eunoia_integer_two_variable_parity.

Lemma eunoia_integer_coefficient_upper : forall x : Z, 2*x <= 3 -> x <= 1.
Proof. cvc5_eunoia. Qed.
Print Assumptions eunoia_integer_coefficient_upper.

Lemma eunoia_integer_coefficient_lower : forall x : Z, 2*x >= 3 -> x >= 2.
Proof. cvc5_eunoia. Qed.
Print Assumptions eunoia_integer_coefficient_lower.

Lemma eunoia_integer_negative_upper : forall x : Z, -2*x <= 3 -> x >= -1.
Proof. cvc5_eunoia. Qed.
Print Assumptions eunoia_integer_negative_upper.

Lemma eunoia_integer_negative_lower : forall x : Z, -2*x >= 3 -> x <= -2.
Proof. cvc5_eunoia. Qed.
Print Assumptions eunoia_integer_negative_lower.

Lemma eunoia_integer_coefficient_three : forall x : Z, 3*x <= 7 -> x <= 2.
Proof. cvc5_eunoia. Qed.
Print Assumptions eunoia_integer_coefficient_three.

Lemma eunoia_integer_coefficient_three_lower : forall x : Z, 3*x >= 7 -> x >= 3.
Proof. cvc5_eunoia. Qed.
Print Assumptions eunoia_integer_coefficient_three_lower.

Lemma eunoia_integer_scoped_coefficient : forall x y z : Z,
  2*x <= 7 /\ (y <= 7 \/ z <= 9) -> x+y <= 10 \/ x+z <= 12.
Proof. cvc5_eunoia. Qed.
Print Assumptions eunoia_integer_scoped_coefficient.

Lemma eunoia_integer_boolean_scope : forall x y z : Z,
  implb ((2*x <=? 7) && ((y <=? 7) || (z <=? 9)))
    ((x+y <=? 10) || (x+z <=? 12)) = true.
Proof. cvc5_eunoia. Qed.
Print Assumptions eunoia_integer_boolean_scope.

Lemma eunoia_integer_uf_cut : forall (f : Z -> Z) (x : Z),
  2*x <= 3 -> x >= 1 -> f x = f 1.
Proof. cvc5_eunoia. Qed.
Print Assumptions eunoia_integer_uf_cut.

Example eunoia_integer_false_controls : True.
Proof.
  Fail assert (forall x : Z, 2*x <= 3 -> x <= 0) by cvc5_eunoia.
  Fail assert (forall x : Z, -2*x <= 3 -> x >= 0) by cvc5_eunoia.
  Fail assert (forall x : Z, 2*x <> 2) by cvc5_eunoia.
  Fail assert (forall x y : Z, 2*x+4*y <> 2) by cvc5_eunoia.
  Fail assert (forall x y : Z, 2*x <= 7 -> y <= 7 -> x+y <= 9) by cvc5_eunoia.
  exact I.
Qed.
Print Assumptions eunoia_integer_false_controls.
