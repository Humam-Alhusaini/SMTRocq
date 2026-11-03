From Stdlib Require Import String List.
From SMTCoq.checker.eunoia Require Import EoSyntax EoRuntime CpcGenerated
  TraceReplay LiaTraceReplay LiaFixtureTests LiaTraceNegativeTests.
From SMTCoq.checker.eunoia Require TightenMutatedGenerated.
Import ListNotations.
Open Scope string_scope.

(** Syntax computation only: these examples do not certify integer semantics. *)
Definition s := Symbol.
Definition u op a := Apply (s op) a.
Definition b op a c := Apply (u op a) c.
Definition q := lia_query lia_strict_shift_decls.
Definition run := derive 500 q "arith-geq-tighten".
Definition difference := b "+" (s "op_1") (b "*" (s "-1") (s "op_0")).
Definition tightened a c increment :=
  b "=" (u "not" (b ">=" a c)) (b ">=" c (b "+" a (s increment))).

Example exact_benchmark_tightening : run [difference; s "1"] [] =
  Some (tightened difference (s "1") "1").
Proof. vm_compute. reflexivity. Qed.
Example symbolic_integer_boundary : run [s "op_0"; s "op_1"] [] =
  Some (tightened (s "op_0") (s "op_1") "1").
Proof. vm_compute. reflexivity. Qed.
Example negative_integer_boundary : run [s "-3"; s "-7"] [] =
  Some (tightened (s "-3") (s "-7") "1").
Proof. vm_compute. reflexivity. Qed.
Example real_left_rejects : run [s "0/1"; s "1"] [] = None.
Proof. vm_compute. reflexivity. Qed.
Example real_right_rejects : run [difference; s "1/1"] [] = None.
Proof. vm_compute. reflexivity. Qed.
Example boolean_left_rejects : run [s "true"; s "1"] [] = None.
Proof. vm_compute. reflexivity. Qed.
Example boolean_right_rejects : run [difference; s "false"] [] = None.
Proof. vm_compute. reflexivity. Qed.
Example mixed_integer_real_sum_rejects :
  run [b "+" (s "op_0") (s "0/1"); s "1"] [] = None.
Proof. vm_compute. reflexivity. Qed.
Example unknown_argument_rejects : run [s "unknown"; s "1"] [] = None.
Proof. vm_compute. reflexivity. Qed.
Example missing_argument_rejects : run [difference] [] = None.
Proof. vm_compute. reflexivity. Qed.
Example extra_argument_rejects : run [difference; s "1"; s "2"] [] = None.
Proof. vm_compute. reflexivity. Qed.
Example unexpected_premise_rejects : run [difference; s "1"] [s "true"] = None.
Proof. vm_compute. reflexivity. Qed.
Example missing_type_query_rejects :
  derive 500 (fun _ => None) "arith-geq-tighten" [difference; s "1"] [] = None.
Proof. vm_compute. reflexivity. Qed.
Definition no_boolean_query t :=
  match q t with Some (Symbol "Bool") => None | ty => ty end.
Example missing_result_type_rejects :
  derive 500 no_boolean_query "arith-geq-tighten" [difference; s "1"] [] = None.
Proof. vm_compute. reflexivity. Qed.
Example exhausted_fuel_rejects : derive 0 q "arith-geq-tighten" [difference; s "1"] [] = None.
Proof. vm_compute. reflexivity. Qed.
Example assumption_on_ordinary_rule_rejects :
  derive_assuming 500 q "arith-geq-tighten" (s "true") [difference; s "1"] [] = None.
Proof. vm_compute. reflexivity. Qed.

(** The mutation is compiled from the actual .eo declaration by the script.
    Its changed result is test data, never a production rule or semantic claim. *)
Example source_increment_mutation_changes_result :
  TightenMutatedGenerated.derive 500 q "arith-geq-tighten" [difference; s "1"] [] =
  Some (tightened difference (s "1") "2").
Proof. vm_compute. reflexivity. Qed.
Example source_increment_mutation_is_not_original :
  match run [difference; s "1"] [],
    TightenMutatedGenerated.derive 500 q "arith-geq-tighten" [difference; s "1"] [] with
  | Some original, Some mutated => term_eqb original mutated
  | _, _ => true
  end = false.
Proof. vm_compute. reflexivity. Qed.

(** All 32 captured commands compute in LiaFixtureTests. Here mutations of
    the actual @p20 must fail, even when its altered arguments are well typed. *)
Example strict_shift_query_arguments :
  q difference = Some (s "Int") /\ q (s "1") = Some (s "Int") /\
  q (tightened difference (s "1") "1") = Some (s "Bool").
Proof. vm_compute. repeat split; reflexivity. Qed.
Example strict_shift_complete_trace_has_no_failure :
  trace_diagnostic q lia_strict_shift_roots [] lia_strict_shift_steps = None.
Proof. vm_compute. reflexivity. Qed.
Definition changed_boundary :=
  map (alter_step (change_args [difference; s "0"]) 20) lia_strict_shift_steps.
Example changed_boundary_breaks_next_transitivity :
  trace_diagnostic q lia_strict_shift_roots [] changed_boundary = Some 21.
Proof. vm_compute. reflexivity. Qed.
Example changed_boundary_rejects_complete_trace :
  trace_final q lia_strict_shift_roots changed_boundary 33 = None.
Proof. vm_compute. reflexivity. Qed.
Example wrong_tightening_type_rejects_at_source_step :
  trace_diagnostic q lia_strict_shift_roots []
    (map (alter_step (change_args [difference; s "1/1"]) 20) lia_strict_shift_steps) = Some 20.
Proof. vm_compute. reflexivity. Qed.
Example extra_tightening_premise_rejects_at_source_step :
  trace_diagnostic q lia_strict_shift_roots []
    (map (alter_step (change_premises [1]) 20) lia_strict_shift_steps) = Some 20.
Proof. vm_compute. reflexivity. Qed.
Definition change_declared result step :=
  {| step_id := step_id step; step_rule := step_rule step;
     step_args := step_args step; step_premises := step_premises step;
     step_declared := Some result |}.
Example changed_tightening_conclusion_rejects_at_source_step :
  trace_diagnostic q lia_strict_shift_roots []
    (map (alter_step (change_declared (tightened difference (s "1") "2")) 20)
      lia_strict_shift_steps) = Some 20.
Proof. vm_compute. reflexivity. Qed.
Example omitted_tightening_rejects_at_source_step :
  trace_diagnostic q lia_strict_shift_roots []
    (map (alter_step (change_rule "unselected-tightening") 20) lia_strict_shift_steps) = Some 20.
Proof. vm_compute. reflexivity. Qed.
Example strict_shift_unused_unknown_step_rejects :
  trace_final q lia_strict_shift_roots (lia_strict_shift_steps ++ [extra_unknown]) 33 = None.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions exact_benchmark_tightening.
Print Assumptions symbolic_integer_boundary.
Print Assumptions negative_integer_boundary.
Print Assumptions real_left_rejects.
Print Assumptions real_right_rejects.
Print Assumptions boolean_left_rejects.
Print Assumptions boolean_right_rejects.
Print Assumptions mixed_integer_real_sum_rejects.
Print Assumptions unknown_argument_rejects.
Print Assumptions missing_argument_rejects.
Print Assumptions extra_argument_rejects.
Print Assumptions unexpected_premise_rejects.
Print Assumptions missing_type_query_rejects.
Print Assumptions missing_result_type_rejects.
Print Assumptions exhausted_fuel_rejects.
Print Assumptions assumption_on_ordinary_rule_rejects.
Print Assumptions source_increment_mutation_changes_result.
Print Assumptions source_increment_mutation_is_not_original.
Print Assumptions strict_shift_query_arguments.
Print Assumptions strict_shift_complete_trace_has_no_failure.
Print Assumptions changed_boundary_breaks_next_transitivity.
Print Assumptions changed_boundary_rejects_complete_trace.
Print Assumptions wrong_tightening_type_rejects_at_source_step.
Print Assumptions extra_tightening_premise_rejects_at_source_step.
Print Assumptions changed_tightening_conclusion_rejects_at_source_step.
Print Assumptions omitted_tightening_rejects_at_source_step.
Print Assumptions strict_shift_unused_unknown_step_rejects.
