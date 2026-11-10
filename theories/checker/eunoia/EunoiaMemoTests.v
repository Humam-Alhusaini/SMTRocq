(* SMTCoq -- distributed under the CeCILL-C licence (see LICENSE). *)
From Stdlib Require Import List String Bool Uint63.
From SMTCoq.checker.fol Require Import State Terms.
From SMTCoq.checker.eunoia Require Import EunoiaChecker EunoiaAdapter
  EunoiaLocal EunoiaScope EunoiaScopedAdapter EunoiaScopedAdapterTests EunoiaMemo.
Import ListNotations.
Local Open Scope uint63_scope.
Local Open Scope string_scope.
Module M := EunoiaMemo.
Module S := EunoiaScopedAdapterTests.

Definition entries :=
 [M.CacheEntry [[4];[5]] [] (S.contradiction 4);
  M.CacheEntry [[5]] [8] (S.scope_false 4 8);
  M.CacheEntry [[8]] [5] S.process_false].
Definition step := @EunoiaChecker.Step EunoiaAdapter.rule_payload M.witness_ref.
Definition done : M.trace := EunoiaScope.Done.
Definition body := EunoiaScope.Next (step 3 [2;1] S.contra_p [] (M.Cached 0)) done.
Definition closing := @EunoiaScope.Discharge EunoiaAdapter.rule_payload M.witness_ref
  3 4 S.scope_p [8] (M.Cached 1).
Definition finish := EunoiaScope.Next (step 5 [4] S.process_p [5] (M.Cached 2))
  (EunoiaScope.Next (step 6 [0;5] S.contra_p [] (M.Cached 0)) done).
Definition shared : M.trace := EunoiaScope.Push 2 4 body (Some closing) finish.
Definition check cache t := @M.checker S.sorts S.funcs S.atoms S.forms S.names
  100 cache 12 S.roots S.root_terms S.claims t 6.
Definition valid cache := @M.cache_valid S.sorts S.funcs S.atoms S.forms cache.
Definition gate := @M.gate S.sorts S.funcs S.atoms S.forms.

Example all_entries_checked : valid entries = true.
Proof. vm_compute; reflexivity. Qed.
Example shared_scoped_refutation : check entries shared = true.
Proof. vm_compute; reflexivity. Qed.
Example missing_cache_rejected : check [] shared = false.
Proof. vm_compute; reflexivity. Qed.
Example ordered_premises_are_exact :
  gate entries [[5];[4]] [] (M.Cached 0) = false.
Proof. vm_compute; reflexivity. Qed.
Example changed_conclusion_rejected :
  gate entries [[4];[5]] [4] (M.Cached 0) = false.
Proof. vm_compute; reflexivity. Qed.
Example out_of_bounds_reference_rejected :
  gate entries [[4];[5]] [] (M.Cached 1000) = false.
Proof. vm_compute; reflexivity. Qed.
Definition invalid_witness := EunoiaLocal.Witness 0 [] [] 0.
Definition invalid := M.CacheEntry [[4]] [] invalid_witness.
Example unused_invalid_entry_rejected : check (entries ++ [invalid]) shared = false.
Proof. vm_compute; reflexivity. Qed.
Example invalid_referenced_entry_rejected :
  check [invalid; nth 1%nat entries invalid; nth 2%nat entries invalid] shared = false.
Proof. vm_compute; reflexivity. Qed.
Example wrong_cached_certificate_rejected :
  check entries (EunoiaScope.Push 2 4
    (EunoiaScope.Next (step 3 [2;1] S.contra_p [] (M.Cached 1)) done)
    (Some closing) finish) = false.
Proof. vm_compute; reflexivity. Qed.
Example invalid_inline_certificate_rejected :
  check entries (EunoiaScope.Push 2 4
    (EunoiaScope.Next (step 3 [2;1] S.contra_p []
      (M.Inline (EunoiaLocal.Witness 0 [] [] 0))) done)
    (Some closing) finish) = false.
Proof. vm_compute; reflexivity. Qed.

Fixpoint inline_trace (t : EunoiaScopedAdapter.trace) : M.trace :=
  match t with
  | EunoiaScope.Done => EunoiaScope.Done
  | EunoiaScope.Next st rest => EunoiaScope.Next
      (step (EunoiaChecker.destination st) (EunoiaChecker.premises st)
        (EunoiaChecker.payload st) (EunoiaChecker.conclusion st)
        (M.Inline (EunoiaChecker.evidence st))) (inline_trace rest)
  | EunoiaScope.Push slot a body closing rest => EunoiaScope.Push slot a
      (inline_trace body)
      (option_map (fun d => @EunoiaScope.Discharge EunoiaAdapter.rule_payload M.witness_ref
        (EunoiaScope.endpoint d) (EunoiaScope.export_slot d) (EunoiaScope.scope_payload d)
        (EunoiaScope.scope_conclusion d) (M.Inline (EunoiaScope.scope_evidence d))) closing)
      (inline_trace rest)
  end.
Example inline_fallback_checks_original_certificates : check [] (inline_trace S.single) = true.
Proof. vm_compute; reflexivity. Qed.
Example generated_rules_are_not_skipped :
  check entries (EunoiaScope.Push 2 4
    (EunoiaScope.Next (step 3 [2;1]
      (EunoiaAdapter.Payload "unsupported" [] [S.p; S.neg S.p] S.f []) [] (M.Cached 0)) done)
    (Some closing) finish) = false.
Proof. vm_compute; reflexivity. Qed.
Example shared_refutation_is_sound : ~ Forall (C.valid S.rho) S.roots.
Proof. eapply M.checker_correct; exact shared_scoped_refutation. Qed.
Print Assumptions shared_refutation_is_sound.
