(**************************************************************************)
(* SMTCoq: checked live cvc5/Eunoia integer arithmetic regressions.         *)
(* Every positive theorem executes the actual public tactic.              *)
(**************************************************************************)
From SMTCoq Require Import SMTRocq.
From Stdlib Require Import Bool ZArith.
Local Open Scope Z_scope.

Lemma eunoia_add_associativity : forall x y z : Z, x+(y+z)=(x+y)+z.
Proof. cvc5_eunoia. Qed.
Print Assumptions eunoia_add_associativity.

Lemma eunoia_add_normalization : forall x y : Z, x + y = y + x.
Proof. cvc5_eunoia. Qed.
Print Assumptions eunoia_add_normalization.

Lemma eunoia_bound_conflict : forall x : Z, x <= 0 -> x >= 1 -> False.
Proof. cvc5_eunoia. Qed.
Print Assumptions eunoia_bound_conflict.

Lemma eunoia_coefficient_negative : forall x y : Z, -2*(x-y) = 2*y-2*x.
Proof. cvc5_eunoia. Qed.
Print Assumptions eunoia_coefficient_negative.

Lemma eunoia_coefficient_normalization : forall x y : Z, 2*(x+y) = 2*x + 2*y.
Proof. cvc5_eunoia. Qed.
Print Assumptions eunoia_coefficient_normalization.

Lemma eunoia_equality_to_bound : forall x : Z, x = 4 -> x <= 4.
Proof. cvc5_eunoia. Qed.
Print Assumptions eunoia_equality_to_bound.

Lemma eunoia_lia_equality_bound : forall (x : Z), implb (x - 3 =? 7) (x >=? 10) = true.
Proof. cvc5_eunoia. Qed.
Print Assumptions eunoia_lia_equality_bound.

Lemma eunoia_lia_integer_gap : forall (x y : Z), implb (x >? y) (y + 1 <=? x) = true.
Proof. cvc5_eunoia. Qed.
Print Assumptions eunoia_lia_integer_gap.

Lemma eunoia_lia_two_sided_bound : forall (x : Z), implb (((x - 3) <=? 7) && (7 <=? (x - 3))) (x >=? 10) = true.
Proof. cvc5_eunoia. Qed.
Print Assumptions eunoia_lia_two_sided_bound.

Lemma eunoia_negative_weakening : forall x : Z, x <= -3 -> x <= -2.
Proof. cvc5_eunoia. Qed.
Print Assumptions eunoia_negative_weakening.

Lemma eunoia_nonpositive_sum : forall x y : Z, x <= 0 -> y <= 0 -> x+y <= 0.
Proof. cvc5_eunoia. Qed.
Print Assumptions eunoia_nonpositive_sum.

Lemma eunoia_nonunit_bound : forall x : Z, (x <= 0 \/ x >= 3) -> x >= 1 -> x <= 2 -> False.
Proof. cvc5_eunoia. Qed.
Print Assumptions eunoia_nonunit_bound.

Lemma eunoia_scoped_bounds : forall x : Z, Bool.eqb (x <=? 0) (negb (x >? 0)) = true.
Proof. cvc5_eunoia. Qed.
Print Assumptions eunoia_scoped_bounds.

Lemma eunoia_subtract_normalization : forall x y : Z, x - y + y = x.
Proof. cvc5_eunoia. Qed.
Print Assumptions eunoia_subtract_normalization.

(* cvc5 emits arith_poly_norm followed by UF congruence for this goal. *)
Lemma eunoia_uf_arithmetic_congruence : forall (f : Z -> Z) (x y : Z),
  f (x+y) = f (y+x).
Proof. cvc5_eunoia. Qed.
Print Assumptions eunoia_uf_arithmetic_congruence.

Example eunoia_lia_false_controls : True.
Proof.
  Fail assert (forall x y : Z, x <= y -> x + 1 <= y) by cvc5_eunoia.
  Fail assert (forall x : Z, 2*x <= 3 -> x <= 0) by cvc5_eunoia.
  exact I.
Qed.
Print Assumptions eunoia_lia_false_controls.

(* Interpreted integer literals must keep arithmetic search enabled. *)
Lemma eunoia_integer_literal_conflict : forall x : Z, x = 0 -> x = 1 -> False.
Proof. cvc5_eunoia. Qed.
Print Assumptions eunoia_integer_literal_conflict.

(* Several actual local hypotheses exercise the ordered root-vector binding. *)
Lemma eunoia_eight_inequality_cycle : forall x0 x1 x2 x3 x4 x5 x6 x7 : Z,
  x0 <= x1 -> x1 <= x2 -> x2 <= x3 -> x3 <= x4 ->
  x4 <= x5 -> x5 <= x6 -> x6 <= x7 -> x7 < x0 -> False.
Proof. cvc5_eunoia. Qed.
Print Assumptions eunoia_eight_inequality_cycle.
Example eunoia_non_strict_cycle_rejected : True.
Proof.
  Fail assert (forall x0 x1 x2 x3 x4 x5 x6 x7 : Z,
    x0 <= x1 -> x1 <= x2 -> x2 <= x3 -> x3 <= x4 ->
    x4 <= x5 -> x5 <= x6 -> x6 <= x7 -> x7 <= x0 -> False) by cvc5_eunoia.
  exact I.
Qed.
Print Assumptions eunoia_non_strict_cycle_rejected.
