Declare ML Module "rocq-smtcoq.kernel_acceptance_probe".
From Stdlib Require Import Bool.
Lemma accepted : true = true.
Proof. kernel_acceptance_true. Qed.
Lemma rejected_before_callback : true = true.
Proof.
 Fail kernel_acceptance_false.
 kernel_acceptance_callback_not_run.
 reflexivity.
Qed.
Print Assumptions accepted.
Print Assumptions rejected_before_callback.

Lemma transparent_data : true = true.
Proof. kernel_data_true. Qed.
Lemma illtyped_data_rejected_before_callback : true = true.
Proof.
 Fail kernel_data_bad_type.
 kernel_acceptance_callback_not_run.
 reflexivity.
Qed.
Print Assumptions transparent_data.
Print Assumptions illtyped_data_rejected_before_callback.
