From Stdlib Require Import String List.
From SMTCoq.checker.eunoia Require Import EoSyntax EoRuntime CpcGenerated TraceReplay FixtureTests MutatedCpcGenerated.
Import ListNotations.
Open Scope string_scope.
Definition unknown_step := {| step_id := 99; step_rule := "unavailable";
  step_args := []; step_premises := []; step_declared := None |}.
Example unused_unknown_step_after_conflict :
  final_term (uf_query uf4_decls) uf4_roots (uf4_steps ++ [unknown_step]) 16 = None.
Proof. vm_compute. reflexivity. Qed.
Example unused_unknown_step_before_conflict :
  final_term (uf_query uf4_decls) uf4_roots (unknown_step :: uf4_steps) 16 = None.
Proof. vm_compute. reflexivity. Qed.
Definition replace_step (s : decoded_step) (i : nat) (steps : list decoded_step) :=
  (firstn i steps ++ s :: skipn (S i) steps)%list.
Definition wrong_index := {| step_id := 6; step_rule := "and_elim";
  step_args := [Symbol "4"]; step_premises := [1]; step_declared := None |}.
Example actual_trace_bad_selection : final_term (uf_query uf4_decls) uf4_roots
  (replace_step wrong_index 4 uf4_steps) 16 = None.
Proof. vm_compute. reflexivity. Qed.
Definition wrong_cong := {| step_id := 4; step_rule := "cong";
  step_args := [Apply (Symbol "not") (Apply (Apply (Symbol "=") (Symbol "x")) (Symbol "x"))];
  step_premises := [3]; step_declared := None |}.
Example actual_trace_repeated_variable_mismatch : final_term (uf_query uf4_decls) uf4_roots
  (replace_step wrong_cong 2 uf4_steps) 16 = None.
Proof. vm_compute. reflexivity. Qed.
Definition extra_premise := {| step_id := 5; step_rule := "trans";
  step_args := []; step_premises := [4; 2; 2]; step_declared := None |}.
Example actual_trace_duplicate_premise_is_checked : final_term (uf_query uf4_decls) uf4_roots
  (replace_step extra_premise 3 uf4_steps) 16 = None.
Proof. vm_compute. reflexivity. Qed.
Definition wrong_result := {| step_id := 16; step_rule := "eq_resolve";
  step_args := []; step_premises := [15; 14]; step_declared := Some (Symbol "true") |}.
Example actual_trace_changed_declared_conclusion : final_term (uf_query uf4_decls) uf4_roots
  (replace_step wrong_result 14 uf4_steps) 16 = None.
Proof. vm_compute. reflexivity. Qed.
Example changed_source_guard_changes_actual_replay :
  replay_with MutatedCpcGenerated.derive (uf_query uf4_decls) uf4_roots uf4_steps = None.
Proof. vm_compute. reflexivity. Qed.
Print Assumptions changed_source_guard_changes_actual_replay.
Print Assumptions unused_unknown_step_after_conflict.
