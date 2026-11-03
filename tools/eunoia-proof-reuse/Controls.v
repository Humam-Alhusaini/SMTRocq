From SMTCoq Require Import SMTCoq.
From SMTCoq.checker.eunoia Require Import EunoiaScopedAdapter.
From Stdlib Require Import Bool ZArith.
Declare ML Module "rocq-smtcoq.eunoia_backend_test".
Local Open Scope Z_scope.

Lemma failed_certificate_rollback (p : bool) : p = p.
Proof.
  Fail backend_corrupted.
  Fail backend_bad_gate.
  Fail backend_bad_unused.
  Fail backend_scoped_bad_discharge.
  Fail backend_scoped_bad_supported_unused.
  backend_no_private_effects.
  Fail Check failed_certificate_rollback_subproof.
  backend_replay.
Qed.
Print Assumptions failed_certificate_rollback.

Lemma source_mutations (x : Z) : (x + 0 =? x) = true.
Proof.
  Fail backend_lia_bad_coefficient.
  Fail backend_lia_bad_premise.
  Fail backend_lia_bad_conclusion.
  Fail backend_lia_bad_root.
  backend_no_private_effects.
  Fail Check source_mutations_subproof.
  backend_lia_replay.
Qed.
Print Assumptions source_mutations.

Lemma witness_mutations (x : Z) :
  implb ((-2 <? 0) && (x >=? 0)) (-2*x <=? -2*0) = true.
Proof.
  Fail backend_lia_missing_certificate.
  Fail backend_lia_bad_unused.
  backend_no_private_effects.
  Fail Check witness_mutations_subproof.
  backend_lia_scale_replay.
Qed.
Print Assumptions witness_mutations.

Lemma scope_bindings (p : bool) : implb p p = true.
Proof.
  Fail backend_scope_bad_assumption.
  Fail backend_scope_bad_root.
  Fail backend_scope_leak.
  Fail backend_scope_bad_endpoint.
  Fail backend_scope_bad_unused.
  backend_no_private_effects.
  Fail Check scope_bindings_subproof.
  backend_scope_required.
Qed.
Print Assumptions scope_bindings.

Lemma missing_intermediate_instance : forall (A B : Type) (HA : CompDec A)
  (f : A -> B) (g : B -> A) (x y : A), x = y -> g (f x) = g (f y).
Proof.
  intros.
  Fail cvc5_eunoia.
  backend_no_private_effects.
  Fail Check missing_intermediate_instance_subproof.
  now subst.
Qed.
Print Assumptions missing_intermediate_instance.

Lemma false_controls : True.
Proof.
  Fail assert ((0 : Z) = 1) by cvc5_eunoia.
  Fail assert (forall (A : Type) (HA : CompDec A)
    (f : A -> A) (x y : A), f x = f y -> x = y) by cvc5_eunoia.
  exact I.
Qed.
Print Assumptions false_controls.

(* Roll back a successful private declaration, then repeat in the same proof. *)
Lemma undo_checked_certificate (p : bool) : p = p.
Proof.
  backend_replay.
  Undo.
  backend_no_private_effects.
  Fail Check undo_checked_certificate_subproof.
  backend_replay.
Qed.
Print Assumptions undo_checked_certificate.

Set Universe Polymorphism.
Section SectionUniverses.
  Context (A B : Type) (HA : CompDec A) (HB : CompDec B).
  Lemma section_carriers (f : A -> B) (g : B -> A) (x y : A) :
    x = y -> g (f x) = g (f y).
  Proof using HA HB. cvc5_eunoia. Qed.
End SectionUniverses.
Unset Universe Polymorphism.
Print Assumptions section_carriers.
