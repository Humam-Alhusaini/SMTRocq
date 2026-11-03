From Stdlib Require Import String List.
From SMTCoq.checker.eunoia Require Import EoSyntax EoRuntime CpcGenerated TraceReplay LiaTraceReplay LiaFixtureTests.
Import ListNotations.
Open Scope string_scope.
Definition alter_step (change : decoded_step -> decoded_step) (id : nat) c :=
  match c with
  | TraceStep s => if Nat.eqb (step_id s) id then TraceStep (change s) else c
  | TracePop s => if Nat.eqb (step_id s) id then TracePop (change s) else c
  | _ => c end.
Definition change_args args s := {| step_id := step_id s; step_rule := step_rule s;
  step_args := args; step_premises := step_premises s; step_declared := step_declared s |}.
Definition change_premises ps s := {| step_id := step_id s; step_rule := step_rule s;
  step_args := step_args s; step_premises := ps; step_declared := step_declared s |}.
Definition change_rule name s := {| step_id := step_id s; step_rule := name;
  step_args := step_args s; step_premises := step_premises s; step_declared := step_declared s |}.
Definition broken_coefficient := Apply (Apply (Symbol "=")
  (Apply (Apply (Symbol "*") (Symbol "-9"))
    (Apply (Apply (Symbol "-") (Apply (Apply (Symbol "+") (Symbol "-3")) (Symbol "x"))) (Symbol "7"))))
  (Apply (Apply (Symbol "*") (Symbol "-10")) (Apply (Apply (Symbol "-") (Symbol "x")) (Symbol "10"))).
Example actual_lia_coefficient_mutation : trace_final (lia_query lia2_decls) lia2_roots
  (map (alter_step (change_args [broken_coefficient]) 7) lia2_steps) 28 = None.
Proof. vm_compute. reflexivity. Qed.
Example actual_lia_missing_premise : trace_final (lia_query lia2_decls) lia2_roots
  (map (alter_step (change_premises []) 8) lia2_steps) 28 = None.
Proof. vm_compute. reflexivity. Qed.
Example actual_lia_changed_guard : trace_final (lia_query lia1_decls) lia1_roots
  (map (alter_step (change_args [Symbol "1";
    Apply (Apply (Symbol ">=") (Apply (Apply (Symbol "+") (Symbol "x")) (Symbol "y"))) (Symbol "11")]) 71) lia1_steps) 128 = None.
Proof. vm_compute. reflexivity. Qed.
Example actual_lia_changed_sum_multiplicity : trace_final (lia_query lia1_decls) lia1_roots
  (map (alter_step (change_premises [78; 75; 75]) 79) lia1_steps) 128 = None.
Proof. vm_compute. reflexivity. Qed.
Example actual_lia_pop_requires_assumption_rule : trace_final (lia_query lia1_decls) lia1_roots
  (map (alter_step (change_rule "refl") 132) lia1_steps) 128 = None.
Proof. vm_compute. reflexivity. Qed.
Definition extra_unknown := TraceStep {| step_id := 999; step_rule := "unknown";
  step_args := []; step_premises := []; step_declared := None |}.
Example actual_lia_unused_unknown_rejects : trace_final (lia_query lia2_decls) lia2_roots
  (lia2_steps ++ [extra_unknown]) 28 = None.
Proof. vm_compute. reflexivity. Qed.
Definition simple id name args ps := {| step_id := id; step_rule := name;
  step_args := args; step_premises := ps; step_declared := None |}.
Definition tq := lia_query [("p", Symbol "Bool")].
Definition local_trace := [TracePush 1 (Symbol "p"); TraceStep (simple 2 "refl" [Symbol "p"] []);
  TracePop (simple 3 "scope" [] [2])].
Example local_steps_are_computed : trace_replay tq [] [] local_trace =
  Some [(3, Apply (Apply (Symbol "=>") (Symbol "p")) (Apply (Apply (Symbol "=") (Symbol "p")) (Symbol "p")))].
Proof. vm_compute. reflexivity. Qed.
Example popped_local_ids_reject : trace_replay tq [] []
  (local_trace ++ [TraceStep (simple 4 "symm" [] [2])]) = None.
Proof. vm_compute. reflexivity. Qed.
Example unclosed_scope_rejects : trace_replay tq [] [] [TracePush 1 (Symbol "p")] = None.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions actual_lia_coefficient_mutation.
Print Assumptions actual_lia_missing_premise.
Print Assumptions actual_lia_changed_guard.
Print Assumptions actual_lia_changed_sum_multiplicity.
Print Assumptions actual_lia_pop_requires_assumption_rule.
Print Assumptions actual_lia_unused_unknown_rejects.
Print Assumptions local_steps_are_computed.
Print Assumptions popped_local_ids_reject.
Print Assumptions unclosed_scope_rejects.
