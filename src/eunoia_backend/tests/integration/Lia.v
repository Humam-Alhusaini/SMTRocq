From SMTCoq Require Import SMTRocq.
From Stdlib Require Import Bool ZArith.
Declare ML Module "rocq-smtcoq.eunoia_backend_test".
Local Open Scope Z_scope.

Lemma backend_lia_source_replay (x : Z) : (x + 0 =? x) = true.
Proof. backend_lia_replay. Qed.
Print Assumptions backend_lia_source_replay.

Example backend_lia_mutations (x : Z) : (x + 0 =? x) = true.
Proof.
  Fail backend_lia_bad_coefficient.
  Fail backend_lia_bad_premise.
  Fail backend_lia_bad_conclusion.
  Fail backend_lia_bad_root.
  backend_lia_replay.
Qed.
Print Assumptions backend_lia_mutations.

Lemma backend_lia_scaling_replay (x : Z) :
  implb ((-2 <? 0) && (x >=? 0)) (-2*x <=? -2*0) = true.
Proof. backend_lia_scale_replay. Qed.
Print Assumptions backend_lia_scaling_replay.

Example backend_lia_certificate_mutations (x : Z) :
  implb ((-2 <? 0) && (x >=? 0)) (-2*x <=? -2*0) = true.
Proof.
  Fail backend_lia_missing_certificate.
  Fail backend_lia_bad_unused.
  backend_lia_scale_replay.
Qed.
Print Assumptions backend_lia_certificate_mutations.

Lemma backend_lia_scoped_replay (x : Z) :
  implb (x >=? 0) (-2*x <=? -2*0) = true.
Proof. backend_lia_scoped. Qed.
Print Assumptions backend_lia_scoped_replay.

Lemma backend_lia_positive_scaling (x : Z) :
  implb ((3 >? 0) && (x <=? 1)) (3*x <=? 3*1) = true.
Proof. backend_lia_positive. Qed.
Print Assumptions backend_lia_positive_scaling.
Example backend_lia_positive_unused_mutation (x : Z) :
  implb ((3 >? 0) && (x <=? 1)) (3*x <=? 3*1) = true.
Proof. Fail backend_lia_positive_bad_unused. backend_lia_positive. Qed.
Print Assumptions backend_lia_positive_unused_mutation.
Lemma backend_lia_lower_tightening (x : Z) :
  implb (x >? -2) (x >=? -1) = true.
Proof. backend_lia_lower. Qed.
Print Assumptions backend_lia_lower_tightening.
Example backend_lia_lower_mutations (x : Z) :
  implb (x >? -2) (x >=? -1) = true.
Proof.
 Fail backend_lia_lower_bad_premise.
 Fail backend_lia_lower_bad_result.
 backend_lia_lower.
Qed.
Print Assumptions backend_lia_lower_mutations.
(* A compound root bypasses the direct-equality ground-value shortcut.
   Disable the Boolean search prefix to exercise Micromega's branch order.
   This previously produced a certificate rejected by the verified checker. *)
Lemma backend_lia_branch_order_regression (x : Z) (hp : ((x =? 7) && true) = true) :
  (x/3 =? 2) = true.
Proof. backend_lia_branch_order. Qed.
Print Assumptions backend_lia_branch_order_regression.

Lemma backend_ground_quotient_value (f : Z -> Z) : (f (7/3) =? f 2) = true.
Proof. backend_live. Qed.
Print Assumptions backend_ground_quotient_value.
Lemma backend_ground_zero_value (f : Z -> Z) : (f (7/0) =? f 0) = true.
Proof. backend_live. Qed.
Print Assumptions backend_ground_zero_value.
Example backend_ground_value_false_controls : True.
Proof.
 Fail assert (forall f : Z -> Z, (f (7/3) =? f 3) = true) by backend_live.
 exact I.
Qed.
Print Assumptions backend_ground_value_false_controls.
