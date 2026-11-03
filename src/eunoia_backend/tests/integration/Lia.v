From SMTCoq Require Import SMTCoq.
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
