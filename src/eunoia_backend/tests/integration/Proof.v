From Stdlib Require Import Bool String List.
From SMTCoq.checker.eunoia Require Import EunoiaAdapter EunoiaLocal EunoiaTactic EunoiaScopedAdapter.
From SMTCoq.checker.eunoia Require Import EunoiaMemo.
Declare ML Module "rocq-smtcoq.eunoia_backend_test".

Lemma replay_reflexive (p:bool) : p = p.
Proof. backend_replay. Qed.
Print Assumptions replay_reflexive.

Lemma replay_with_lemma (p:bool) (hp:p=true) : p = p.
Proof. backend_with_lemma. Qed.
Print Assumptions replay_with_lemma.

Lemma replay_true (p:bool) : Bool.eqb p p = true.
Proof. backend_replay. Qed.
Print Assumptions replay_true.

Lemma replay_false (p:bool) : negb (Bool.eqb p p) = false.
Proof. backend_replay. Qed.
Print Assumptions replay_false.

Lemma checked_rejections_and_live (p:bool) : p = p.
Proof.
  Fail backend_corrupted.
  Fail backend_bad_gate.
  Fail backend_bad_unused.
  backend_live.
Qed.
Print Assumptions checked_rejections_and_live.

Lemma scoped_replay_reflexive (p:bool) : p = p.
Proof.
  Fail backend_scoped_bad_discharge.
  Fail backend_scoped_bad_supported_unused.
  backend_scoped.
Qed.
Print Assumptions scoped_replay_reflexive.

Lemma nested_scoped_replay_reflexive (p:bool) : p = p.
Proof. backend_scoped_nested. Qed.
Print Assumptions nested_scoped_replay_reflexive.

Lemma scoped_export_required (p:bool) : implb p p = true.
Proof.
  Fail backend_scope_bad_assumption.
  Fail backend_scope_bad_root.
  Fail backend_scope_leak.
  Fail backend_scope_bad_endpoint.
  Fail backend_scope_bad_unused.
  backend_scope_required.
Qed.
Print Assumptions scoped_export_required.

Lemma nested_scoped_export_required (p q:bool) : implb p (implb q p) = true.
Proof. backend_scope_required_nested. Qed.
Print Assumptions nested_scoped_export_required.

Lemma scoped_export_false (p:bool) : negb (implb p p) = false.
Proof. backend_scope_required. Qed.
Print Assumptions scoped_export_false.

Lemma signature_metadata_replay (p:bool) : p = p.
Proof. backend_metadata_replay. Qed.
Print Assumptions signature_metadata_replay.
Example shared_encoding_preserves_source : True.
Proof. backend_encoding. exact I. Qed.
