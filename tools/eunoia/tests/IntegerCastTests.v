From Stdlib Require Import String List.
From SMTCoq.checker.eunoia Require Import EoSyntax EoRuntime EoArithmetic CpcGenerated
  TraceReplay LiaTraceReplay LiaTraceNegativeTests StrictShiftTests IntegerFixtureTests.
From SMTCoq.checker.eunoia Require IntEqPremiseMutated IntEqResultMutated
  IntGeqPremiseMutated IntGeqResultMutated IntFloorMutated IntCastMutated IntPolyGuardMutated.
Import ListNotations.
Open Scope string_scope.

(** Only source syntax computation. These proofs are not semantic acceptance
    certificates, and the query is deterministic syntax metadata for tests. *)
Definition s := Symbol.
Definition u op a := Apply (s op) a.
Definition b op a c := Apply (u op a) c.
Definition eq := b "=".
Definition x := s "x".
Definition half := s "1/2".
Definition negative_half := s "-3/2".
Definition q := lia_query [("x", s "Int"); ("y", s "Int");
  ("r", s "Real"); ("p", s "Bool"); ("f", arrow (s "Int") (s "Int"))].
Definition fractional c := eq (u "to_real" (u "to_int" c)) c.
Definition guard c := eq (fractional c) (s "false").
Definition increment c := b "+" (u "to_int" c) (s "1").
Definition conflict t c := eq (eq (u "to_real" t) c) (s "false").
Definition tightened t c n := eq (b ">=" (u "to_real" t) c) (b ">=" t n).
Definition run := derive 500 q.
Definition negx := b "*" (s "-1") x.
Definition geq_premises := [guard negative_half; eq (s "-1") (increment negative_half)].

Example positive_floor : run "evaluate" [u "to_int" half] [] =
  Some (eq (u "to_int" half) (s "0")).
Proof. vm_compute. reflexivity. Qed.
Example negative_floor : run "evaluate" [u "to_int" negative_half] [] =
  Some (eq (u "to_int" negative_half) (s "-2")).
Proof. vm_compute. reflexivity. Qed.
Example integral_rational_floor : run "evaluate" [u "to_int" (s "3/1")] [] =
  Some (eq (u "to_int" (s "3/1")) (s "3")).
Proof. vm_compute. reflexivity. Qed.
Example exact_integer_to_rational : run "evaluate" [u "to_real" (s "2")] [] =
  Some (eq (u "to_real" (s "2")) (s "2/1")).
Proof. vm_compute. reflexivity. Qed.
Example actual_fraction_guard : run "evaluate" [fractional half] [] = Some (guard half).
Proof. vm_compute. reflexivity. Qed.
Example actual_negative_guard : run "evaluate" [fractional negative_half] [] = Some (guard negative_half).
Proof. vm_compute. reflexivity. Qed.
Example exact_conflict : run "arith-int-eq-conflict" [x; half] [guard half] = Some (conflict x half).
Proof. vm_compute. reflexivity. Qed.
Example exact_negative_tightening :
  run "arith-int-geq-tighten" [negx; negative_half; s "-1"] geq_premises =
  Some (tightened negx negative_half (s "-1")).
Proof. vm_compute. reflexivity. Qed.
Example integer_literal_cannot_replace_rational :
  run "arith-int-eq-conflict" [x; s "1"] [guard (s "1")] = None.
Proof. vm_compute. reflexivity. Qed.
Example rational_literal_cannot_replace_integer :
  run "arith-int-eq-conflict" [half; half] [guard half] = None.
Proof. vm_compute. reflexivity. Qed.
Example decimal_category_preserved :
  EoArithmetic.eval "eo::is_q" [s "2.0"] = Some (s "false") /\
  EoArithmetic.eval "eo::is_z" [s "2/1"] = Some (s "false").
Proof. vm_compute. split; reflexivity. Qed.
Example wrong_cast_inputs_reject :
  q (u "to_real" half) = None /\ q (u "to_int" (s "2")) = None /\
  q (u "to_int" (s "p")) = None /\ q (u "to_real" (s "unknown")) = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
Example faithful_declared_syntax_types :
  q (s "2.0") = Some (s "Real") /\
  q (u "to_real" negx) = Some (s "Real") /\
  q (u "to_int" negative_half) = Some (s "Int") /\
  q (b "*" (s "3/2") (u "to_real" x)) = Some (s "Real") /\
  q (b "+" (s "r") half) = Some (s "Real") /\
  q (Apply (s "f") x) = Some (s "Int").
Proof. vm_compute. repeat split; reflexivity. Qed.
Example invalid_expressions_reject :
  q (b "+" x half) = None /\ q (b "*" (s "p") (s "p")) = None /\
  q (b ">=" (s "p") (s "p")) = None /\ q (Apply (s "f") half) = None /\
  q (u "to_real" (s "1/0")) = None /\ q (s "unknown") = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
Example missing_conflict_premise_rejects : run "arith-int-eq-conflict" [x; half] [] = None.
Proof. vm_compute. reflexivity. Qed.
Example wrong_fraction_premise_rejects :
  run "arith-int-eq-conflict" [x; half] [guard negative_half] = None.
Proof. vm_compute. reflexivity. Qed.
Example true_guard_premise_rejects :
  run "arith-int-eq-conflict" [x; half] [eq (fractional half) (s "true")] = None.
Proof. vm_compute. reflexivity. Qed.
Example true_integral_guard_does_not_match_conflict :
  run "arith-int-eq-conflict" [x; s "1/1"] [eq (fractional (s "1/1")) (s "true")] = None.
Proof. vm_compute. reflexivity. Qed.
Example extra_conflict_premise_rejects :
  run "arith-int-eq-conflict" [x; half] [guard half; guard half] = None.
Proof. vm_compute. reflexivity. Qed.
Example wrong_bound_premise_rejects :
  run "arith-int-geq-tighten" [negx; negative_half; s "0"] geq_premises = None.
Proof. vm_compute. reflexivity. Qed.
Example reversed_tightening_premises_reject :
  run "arith-int-geq-tighten" [negx; negative_half; s "-1"] (rev geq_premises) = None.
Proof. vm_compute. reflexivity. Qed.
Example missing_tightening_premise_rejects :
  run "arith-int-geq-tighten" [negx; negative_half; s "-1"] [guard negative_half] = None.
Proof. vm_compute. reflexivity. Qed.
Example rational_bound_rejects :
  run "arith-int-geq-tighten" [negx; negative_half; s "-1/1"]
    [guard negative_half; eq (s "-1/1") (increment negative_half)] = None.
Proof. vm_compute. reflexivity. Qed.
Example missing_type_query_rejects :
  derive 500 (fun _ => None) "arith-int-eq-conflict" [x; half] [guard half] = None.
Proof. vm_compute. reflexivity. Qed.
Example unsupported_rule_stays_closed : run "arith-real-unselected" [x; half] [] = None.
Proof. vm_compute. reflexivity. Qed.

(** Source corruption changes executable data and is rejected by an original
    premise/result or by a later step in the complete original capture. *)
Example source_conflict_premise_mutation_rejects :
  IntEqPremiseMutated.derive 500 q "arith-int-eq-conflict" [x; half] [guard half] = None.
Proof. vm_compute. reflexivity. Qed.
Example source_conflict_result_mutation_changes_result :
  IntEqResultMutated.derive 500 q "arith-int-eq-conflict" [x; half] [guard half] =
  Some (eq (eq (u "to_real" x) half) (s "true")).
Proof. vm_compute. reflexivity. Qed.
Example source_tightening_premise_mutation_rejects :
  IntGeqPremiseMutated.derive 500 q "arith-int-geq-tighten" [negx; negative_half; s "-1"] geq_premises = None.
Proof. vm_compute. reflexivity. Qed.
Example source_tightening_result_mutation_changes_result :
  IntGeqResultMutated.derive 500 q "arith-int-geq-tighten" [negx; negative_half; s "-1"] geq_premises =
  Some (eq (b ">=" (u "to_real" negx) negative_half) (b ">" negx (s "-1"))).
Proof. vm_compute. reflexivity. Qed.
Example source_floor_mutation_changes_result :
  IntFloorMutated.derive 500 q "evaluate" [u "to_int" negative_half] [] =
  Some (eq (u "to_int" negative_half) (s "2")).
Proof. vm_compute. reflexivity. Qed.
Example source_cast_mutation_preserves_literal_distinction :
  IntCastMutated.derive 500 q "evaluate" [u "to_real" (s "2")] [] = None.
Proof. vm_compute. reflexivity. Qed.
Example IntEqPremiseMutated_rejects_original_complete_capture :
  trace_final_with IntEqPremiseMutated.derive IntEqPremiseMutated.derive_assuming
    (lia_query lia_parity_decls) lia_parity_roots lia_parity_steps 9 = None.
Proof. vm_compute. reflexivity. Qed.
Example IntEqResultMutated_rejects_original_complete_capture :
  trace_final_with IntEqResultMutated.derive IntEqResultMutated.derive_assuming
    (lia_query lia_parity_decls) lia_parity_roots lia_parity_steps 9 = None.
Proof. vm_compute. reflexivity. Qed.
Example IntGeqPremiseMutated_rejects_original_complete_capture :
  trace_final_with IntGeqPremiseMutated.derive IntGeqPremiseMutated.derive_assuming
    (lia_query lia_coefficient_bound_decls) lia_coefficient_bound_roots lia_coefficient_bound_steps 18 = None.
Proof. vm_compute. reflexivity. Qed.
Example IntGeqResultMutated_rejects_original_complete_capture :
  trace_final_with IntGeqResultMutated.derive IntGeqResultMutated.derive_assuming
    (lia_query lia_coefficient_bound_decls) lia_coefficient_bound_roots lia_coefficient_bound_steps 18 = None.
Proof. vm_compute. reflexivity. Qed.
Example IntFloorMutated_rejects_original_complete_capture :
  trace_final_with IntFloorMutated.derive IntFloorMutated.derive_assuming
    (lia_query lia_coefficient_bound_decls) lia_coefficient_bound_roots lia_coefficient_bound_steps 18 = None.
Proof. vm_compute. reflexivity. Qed.
Example IntCastMutated_rejects_original_complete_capture :
  trace_final_with IntCastMutated.derive IntCastMutated.derive_assuming
    (lia_query lia_parity_decls) lia_parity_roots lia_parity_steps 9 = None.
Proof. vm_compute. reflexivity. Qed.
Example IntPolyGuardMutated_rejects_original_complete_capture :
  trace_final_with IntPolyGuardMutated.derive IntPolyGuardMutated.derive_assuming
    (lia_query lia_coefficient_bound_decls) lia_coefficient_bound_roots lia_coefficient_bound_steps 18 = None.
Proof. vm_compute. reflexivity. Qed.

(** Exact mutations of the real source steps, retaining all other commands. *)
Definition parity_q := lia_query lia_parity_decls.
Definition bound_q := lia_query lia_coefficient_bound_decls.
Example actual_parity_wrong_premise_rejects :
  trace_diagnostic parity_q lia_parity_roots []
    (map (alter_step (change_premises [1]) 3) lia_parity_steps) = Some 3.
Proof. vm_compute. reflexivity. Qed.
Example actual_parity_wrong_result_rejects :
  trace_diagnostic parity_q lia_parity_roots []
    (map (alter_step (change_declared (s "true")) 3) lia_parity_steps) = Some 3.
Proof. vm_compute. reflexivity. Qed.
Example actual_parity_changed_fraction_rejects :
  trace_final parity_q lia_parity_roots
    (map (alter_step (change_args [x; s "3/2"]) 3) lia_parity_steps) 9 = None.
Proof. vm_compute. reflexivity. Qed.
Example actual_bound_wrong_premises_reject :
  trace_diagnostic bound_q lia_coefficient_bound_roots []
    (map (alter_step (change_premises [9; 10]) 11) lia_coefficient_bound_steps) = Some 11.
Proof. vm_compute. reflexivity. Qed.
Example actual_bound_wrong_result_rejects :
  trace_diagnostic bound_q lia_coefficient_bound_roots []
    (map (alter_step (change_declared (s "true")) 11) lia_coefficient_bound_steps) = Some 11.
Proof. vm_compute. reflexivity. Qed.
Example actual_bound_wrong_increment_rejects :
  trace_diagnostic bound_q lia_coefficient_bound_roots []
    (map (alter_step (change_args [negx; negative_half; s "0"]) 11)
      lia_coefficient_bound_steps) = Some 11.
Proof. vm_compute. reflexivity. Qed.
Example unused_unknown_step_is_not_skipped :
  trace_final parity_q lia_parity_roots (lia_parity_steps ++ [extra_unknown]) 9 = None.
Proof. vm_compute. reflexivity. Qed.
Example actual_scoped_capture_computes_every_command :
  trace_diagnostic (lia_query lia_coefficient_scoped_decls) lia_coefficient_scoped_roots []
    lia_coefficient_scoped_steps = None.
Proof. vm_compute. reflexivity. Qed.

(** Polymorphic relation instances use their real operand sorts. Merely
    supplying an unknown function name never grants polymorphic matching. *)
Definition rel_pattern := PApply (PApply (PVar 0) (PVar 1)) (PVar 2).
Example source_declared_polymorphic_relation_instances :
  match collect_application_hints_with_polymorphic cpc_polymorphic_operators q
    [rel_pattern; PApply (PApply (PVar 0) (PVar 3)) (PVar 4)]
    [eq x (s "1"); eq (u "to_real" x) half] [] with
  | Some _ => true | _ => false end = true.
Proof. vm_compute. reflexivity. Qed.
Example old_monomorphic_hint_path_still_rejects :
  collect_application_hints q
    [rel_pattern; PApply (PApply (PVar 0) (PVar 3)) (PVar 4)]
    [eq x (s "1"); eq (u "to_real" x) half] [] = None.
Proof. vm_compute. reflexivity. Qed.
Example conflicting_ordinary_value_hints_reject :
  collect_application_hints_with_polymorphic cpc_polymorphic_operators q
    [PVar 0; PVar 0] [x; half] [] = None.
Proof. vm_compute. reflexivity. Qed.
Example missing_polymorphic_metadata_rejects :
  collect_application_hints_with_polymorphic ["unrelated"] q
    [rel_pattern; PApply (PApply (PVar 0) (PVar 3)) (PVar 4)]
    [eq x (s "1"); eq (u "to_real" x) half] [] = None.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions positive_floor.
Print Assumptions negative_floor.
Print Assumptions integral_rational_floor.
Print Assumptions exact_integer_to_rational.
Print Assumptions actual_fraction_guard.
Print Assumptions actual_negative_guard.
Print Assumptions exact_conflict.
Print Assumptions exact_negative_tightening.
Print Assumptions integer_literal_cannot_replace_rational.
Print Assumptions rational_literal_cannot_replace_integer.
Print Assumptions decimal_category_preserved.
Print Assumptions wrong_cast_inputs_reject.
Print Assumptions faithful_declared_syntax_types.
Print Assumptions invalid_expressions_reject.
Print Assumptions missing_conflict_premise_rejects.
Print Assumptions wrong_fraction_premise_rejects.
Print Assumptions true_guard_premise_rejects.
Print Assumptions true_integral_guard_does_not_match_conflict.
Print Assumptions extra_conflict_premise_rejects.
Print Assumptions wrong_bound_premise_rejects.
Print Assumptions reversed_tightening_premises_reject.
Print Assumptions missing_tightening_premise_rejects.
Print Assumptions rational_bound_rejects.
Print Assumptions missing_type_query_rejects.
Print Assumptions unsupported_rule_stays_closed.
Print Assumptions source_conflict_premise_mutation_rejects.
Print Assumptions source_conflict_result_mutation_changes_result.
Print Assumptions source_tightening_premise_mutation_rejects.
Print Assumptions source_tightening_result_mutation_changes_result.
Print Assumptions source_floor_mutation_changes_result.
Print Assumptions source_cast_mutation_preserves_literal_distinction.
Print Assumptions IntEqPremiseMutated_rejects_original_complete_capture.
Print Assumptions IntEqResultMutated_rejects_original_complete_capture.
Print Assumptions IntGeqPremiseMutated_rejects_original_complete_capture.
Print Assumptions IntGeqResultMutated_rejects_original_complete_capture.
Print Assumptions IntFloorMutated_rejects_original_complete_capture.
Print Assumptions IntCastMutated_rejects_original_complete_capture.
Print Assumptions IntPolyGuardMutated_rejects_original_complete_capture.
Print Assumptions actual_parity_wrong_premise_rejects.
Print Assumptions actual_parity_wrong_result_rejects.
Print Assumptions actual_parity_changed_fraction_rejects.
Print Assumptions actual_bound_wrong_premises_reject.
Print Assumptions actual_bound_wrong_result_rejects.
Print Assumptions actual_bound_wrong_increment_rejects.
Print Assumptions unused_unknown_step_is_not_skipped.
Print Assumptions actual_scoped_capture_computes_every_command.
Print Assumptions source_declared_polymorphic_relation_instances.
Print Assumptions old_monomorphic_hint_path_still_rejects.
Print Assumptions conflicting_ordinary_value_hints_reject.
Print Assumptions missing_polymorphic_metadata_rejects.
