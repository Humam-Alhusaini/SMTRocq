From SMTCoq Require Import SMTCoq.
From Stdlib Require Import Bool ZArith.
Local Open Scope Z_scope.
Lemma positive_remainder : forall x : Z, (0 <=? x mod 3) && (x mod 3 <? 3) = true.
Proof. cvc5_eunoia. Qed.
Print Assumptions positive_remainder.
Lemma positive_reconstruction : forall x : Z, (x =? 3*(x/3)+x mod 3) = true.
Proof. cvc5_eunoia. Qed.
Print Assumptions positive_reconstruction.
Lemma positive_quotient_bound : forall x : Z, (3*(x/3) <=? x) = true.
Proof. cvc5_eunoia. Qed.
Print Assumptions positive_quotient_bound.
Lemma negative_remainder : forall x : Z, (-3 <? x mod (-3)) && (x mod (-3) <=? 0) = true.
Proof. cvc5_eunoia. Qed.
Print Assumptions negative_remainder.
Lemma negative_quotient_bound : forall x : Z, (x <=? (-3)*(x/(-3))) = true.
Proof. cvc5_eunoia. Qed.
Print Assumptions negative_quotient_bound.
Lemma zero_divisor : forall x : Z, (x/0 =? 0) && (x mod 0 =? x) = true.
Proof. cvc5_eunoia. Qed.
Print Assumptions zero_divisor.
Lemma ground_divisor_expression : forall x : Z, (x mod (1+2) <? 3) = true.
Proof. cvc5_eunoia. Qed.
Print Assumptions ground_divisor_expression.
Lemma nested_division : forall x : Z, (0 <=? (x/3) mod 5) && ((x/3) mod 5 <? 5) = true.
Proof. cvc5_eunoia. Qed.
Print Assumptions nested_division.
Lemma division_uf : forall (f : Z -> Z) (x : Z), (f (3*(x/3)+x mod 3) =? f x) = true.
Proof. cvc5_eunoia. Qed.
Print Assumptions division_uf.
Example false_controls : True.
Proof.
 Fail assert (forall x : Z, (x mod 3 <? 0) = true) by cvc5_eunoia.
 Fail assert (forall x : Z, (x / 3 =? x) = true) by cvc5_eunoia.
 Fail assert (forall x : Z, (x mod (-3) <=? -1) = true) by cvc5_eunoia.
 exact I.
Qed.
Print Assumptions false_controls.

Lemma quotient_from_hypothesis : forall x : Z, x = 7 -> x/3 = 2.
Proof. cvc5_eunoia. Qed.
Print Assumptions quotient_from_hypothesis.
Lemma negative_numerator : forall x : Z, x = -7 -> x/3 = -3.
Proof. cvc5_eunoia. Qed.
Print Assumptions negative_numerator.
Lemma negative_divisor_from_hypothesis : forall x : Z, x = 7 -> x/(-3) = -3.
Proof. cvc5_eunoia. Qed.
Print Assumptions negative_divisor_from_hypothesis.
Lemma division_only_in_hypotheses : forall x : Z, x < 0 -> x/3 >= 0 -> False.
Proof. cvc5_eunoia. Qed.
Print Assumptions division_only_in_hypotheses.
Lemma two_divisors : forall x : Z,
  (0 <=? x mod 3) && (x mod 3 <? 3) && (0 <=? x mod 5) && (x mod 5 <? 5) = true.
Proof. cvc5_eunoia. Qed.
Print Assumptions two_divisors.
Lemma modulo_periodicity : forall x : Z, (x+3) mod 3 = x mod 3.
Proof. cvc5_eunoia. Qed.
Print Assumptions modulo_periodicity.
Lemma modulo_congruence : forall x y : Z, x = y -> x mod 3 = y mod 3.
Proof. cvc5_eunoia. Qed.
Print Assumptions modulo_congruence.
Lemma nonnegative_quotient_bound : forall x : Z, 0 <= x -> x/3 <= x.
Proof. cvc5_eunoia. Qed.
Print Assumptions nonnegative_quotient_bound.
Lemma quotient_monotonicity : forall x y : Z, x <= y -> x/3 <= y/3.
Proof. cvc5_eunoia. Qed.
Print Assumptions quotient_monotonicity.
Lemma nested_quotient : forall x : Z, (x/3)/5 = x/15.
Proof. cvc5_eunoia. Qed.
Print Assumptions nested_quotient.
Lemma division_abstract_argument : forall (A : Type) (HA : CompDec A) (f : A -> Z) (a : A),
  (0 <=? (f a) mod 3) && ((f a) mod 3 <? 3) = true.
Proof. cvc5_eunoia. Qed.
Print Assumptions division_abstract_argument.
Example division_false_extensions : True.
Proof.
 Fail assert (forall x : Z, x mod 0 = 0) by cvc5_eunoia.
 Fail assert (forall x : Z, (x+1) mod 3 = x mod 3) by cvc5_eunoia.
 Fail assert (forall x : Z, x = -7 -> x/3 = -2) by cvc5_eunoia.
 exact I.
Qed.
Print Assumptions division_false_extensions.

Lemma negative_modulo_shift : forall x : Z, (x+6) mod (-3) = x mod (-3).
Proof. cvc5_eunoia. Qed.
Print Assumptions negative_modulo_shift.
Lemma positive_division_shift : forall x : Z, (x+6)/3 = x/3+2.
Proof. cvc5_eunoia. Qed.
Print Assumptions positive_division_shift.
Lemma negative_division_shift : forall x : Z, (x+6)/(-3) = x/(-3)-2.
Proof. cvc5_eunoia. Qed.
Print Assumptions negative_division_shift.
Lemma subtraction_modulo_shift : forall x : Z, (x-6) mod 3 = x mod 3.
Proof. cvc5_eunoia. Qed.
Print Assumptions subtraction_modulo_shift.
Lemma negative_nested_quotient : forall x : Z, (x/(-3))/5 = x/(-15).
Proof. cvc5_eunoia. Qed.
Print Assumptions negative_nested_quotient.
Lemma large_divisor : forall x : Z,
  (0 <=? x mod 123456789012345678901234567890) &&
  (x mod 123456789012345678901234567890 <? 123456789012345678901234567890) = true.
Proof. cvc5_eunoia. Qed.
Print Assumptions large_divisor.
Lemma both_shift_operations : forall x : Z,
  ((x+6) mod 3 =? x mod 3) && ((x+6)/3 =? x/3+2) = true.
Proof. cvc5_eunoia. Qed.
Print Assumptions both_shift_operations.
Example false_algebra_controls : True.
Proof.
 Fail assert (forall x : Z, (x+6)/(-3) = x/(-3)+2) by cvc5_eunoia.
 Fail assert (forall x : Z, (x/3)/(-5) = x/(-15)) by cvc5_eunoia.
 exact I.
Qed.
Print Assumptions false_algebra_controls.

Lemma known_value_reverse_equality : forall x : Z,
  (7 =? x) = true -> (x/3 =? 2) = true.
Proof. cvc5_eunoia. Qed.
Print Assumptions known_value_reverse_equality.
Lemma known_value_remainder : forall x : Z, x = -7 -> x mod 3 = 2.
Proof. cvc5_eunoia. Qed.
Print Assumptions known_value_remainder.
Lemma known_value_negative_remainder : forall x : Z, x = 7 -> x mod (-3) = -2.
Proof. cvc5_eunoia. Qed.
Print Assumptions known_value_negative_remainder.
Lemma known_value_ground_expression : forall x : Z, x = 4+3 -> x/(-3) = -3.
Proof. cvc5_eunoia. Qed.
Print Assumptions known_value_ground_expression.
Lemma known_value_uf_result : forall (f : Z -> Z) (x : Z), f x = 7 -> (f x)/3 = 2.
Proof. cvc5_eunoia. Qed.
Print Assumptions known_value_uf_result.
Example known_value_false_controls : True.
Proof.
 Fail assert (forall x : Z, (7 =? x) = true -> (x/3 =? 3) = true) by cvc5_eunoia.
 Fail assert (forall x : Z, x = -7 -> x mod 3 = -1) by cvc5_eunoia.
 Fail assert (forall (f : Z -> Z) (x : Z), f x = 7 -> (f x)/3 = 3) by cvc5_eunoia.
 exact I.
Qed.
Print Assumptions known_value_false_controls.
