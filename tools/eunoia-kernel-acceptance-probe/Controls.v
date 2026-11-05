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
