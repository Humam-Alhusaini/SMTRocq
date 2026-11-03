From Stdlib Require Import String List Bool.
From SMTCoq.checker.eunoia Require Import EoSyntax EoRuntime CpcGenerated TestGenerated MutatedGenerated.
Import ListNotations.
Open Scope string_scope.

Definition unary (s : string) (a : term) := Apply (Symbol s) a.
Definition binary (s : string) (a b : term) := Apply (unary s a) b.
Definition x := Symbol "x".
Definition y := Symbol "y".
Definition p := Symbol "p".
Definition q := Symbol "q".
Definition eqxy := binary "=" x y.

(** Deliberately partial mock query. This is test input, never a semantic
    interpretation. In production the coordinator must supply the checked
    SMTCoq adapter; arbitrary queries must not authorize State insertions. *)
Definition query (t : term) : option term :=
  match t with
  | Symbol "x" | Symbol "y" => Some (Symbol "U")
  | Symbol "z" => Some (Symbol "Int")
  | Symbol "U" | Symbol "Int" | Symbol "Bool" => Some (Symbol "Type")
  | Symbol "p" | Symbol "q" | Symbol "true" | Symbol "false" => Some (Symbol "Bool")
  | Apply _ _ => Some (Symbol "Bool")
  | _ => None
  end.

Definition cpc := CpcGenerated.derive 100 query.
Definition test := TestGenerated.derive 100 query.

Example polymorphic_refl : cpc "refl" [x] [] = Some (binary "=" x x).
Proof. reflexivity. Qed.
Example generated_rewrite : cpc "eq-refl" [x] [] =
    Some (binary "=" (binary "=" x x) (Symbol "true")).
Proof. reflexivity. Qed.
Example helper_symmetry : cpc "symm" [] [eqxy] = Some (binary "=" y x).
Proof. reflexivity. Qed.
Example helper_second_case : cpc "symm" [] [unary "not" eqxy] =
    Some (unary "not" (binary "=" y x)).
Proof. reflexivity. Qed.
Example helper_no_case : cpc "symm" [] [p] = None.
Proof. reflexivity. Qed.
Example permissive_query_is_not_semantic_evidence : cpc "symm" [] [binary "=" x (Symbol "z")] = Some (binary "=" (Symbol "z") x).
Proof. reflexivity. Qed.
Example exact_premises : cpc "eq_resolve" [] [p; binary "=" p q] = Some q.
Proof. reflexivity. Qed.
Example repeated_variable_mismatch : cpc "eq_resolve" [] [q; binary "=" p q] = None.
Proof. reflexivity. Qed.
Example reordered_premises : cpc "eq_resolve" [] [binary "=" p q; p] = None.
Proof. reflexivity. Qed.
Example missing_premise : cpc "eq_resolve" [] [p] = None.
Proof. reflexivity. Qed.
Example extra_premise : cpc "eq_resolve" [] [p; binary "=" p q; q] = None.
Proof. reflexivity. Qed.
Example args_cannot_consume_premises : cpc "eq_resolve" [p] [binary "=" p q] = None.
Proof. reflexivity. Qed.
Example type_mismatch : cpc "true_intro" [] [x] = None.
Proof. reflexivity. Qed.
Example missing_type : cpc "refl" [Symbol "unknown"] [] = None.
Proof. reflexivity. Qed.
Example unknown_rule : cpc "made_up" [p] [] = None.
Proof. reflexivity. Qed.
Example excluded_rule : cpc "trust" [p] [] = None.
Proof. reflexivity. Qed.
Example no_fuel : CpcGenerated.derive 0 query "refl" [x] [] = None.
Proof. reflexivity. Qed.
Example side_condition_accept : test "require_equal" [p; p] [] = Some p.
Proof. reflexivity. Qed.
Example side_condition_reject : test "require_equal" [p; q] [] = None.
Proof. reflexivity. Qed.
Example helper_requires_accept : test "guarded" [] [binary "=" x x] = Some (binary "=" x x).
Proof. reflexivity. Qed.
Example helper_requires_reject : test "guarded" [] [eqxy] = None.
Proof. reflexivity. Qed.
Example recursive_helper : test "peel" [unary "not" (unary "not" p)] [] = Some p.
Proof. reflexivity. Qed.
Example recursive_fuel_exhaustion : TestGenerated.derive 2 query "peel" [unary "not" p] [] = None.
Proof. reflexivity. Qed.
Example helper_conditional_true : test "choose" [p; p] [] = Some p.
Proof. reflexivity. Qed.
Example helper_conditional_false : test "choose" [p; q] [] = Some q.
Proof. reflexivity. Qed.
Example changed_signature_changes_computation : MutatedGenerated.derive 100 query
    "choose" [p; q] [] = Some p.
Proof. reflexivity. Qed.
Example typeof_and_let : test "inspect" [p] [] = Some p.
Proof. reflexivity. Qed.
Example failed_body_cannot_fall_through : test "first_match" [p] [] = None.
Proof. reflexivity. Qed.
Example helper_annotations_are_metadata : TestGenerated.derive 100
  (fun t => if term_eqb t (Symbol "true") then None else query t) "output_type" [p] [] = Some (unary "not" (Symbol "true")).
Proof. reflexivity. Qed.

Print Assumptions helper_symmetry.
Print Assumptions side_condition_reject.

Example unused_failure_is_unforced : test "unused_failure" [p] [] = Some p.
Proof. reflexivity. Qed.
Example unselected_branch_is_unforced : test "lazy_branch" [p] [] = Some p.
Proof. reflexivity. Qed.
Example equal_errors_do_not_satisfy_requires : test "failed_values_not_equal" [p] [] = None.
Proof. reflexivity. Qed.
Example is_eq_can_observe_failure : test "failure_predicates" [p] [] = Some (Symbol "false").
Proof. reflexivity. Qed.
Example is_ok_can_observe_failure : test "failure_ok" [p] [] = Some (Symbol "false").
Proof. reflexivity. Qed.
Example lexical_definition_no_capture : test "definition_capture" [p] [] = Some p.
Proof. reflexivity. Qed.
Example parallel_let_uses_outer_scope : test "parallel_shadow" [p] [] = Some p.
Proof. reflexivity. Qed.

Definition and_op := Symbol "and".
Definition true_nil := Symbol "true".
Definition and_list := make_list and_op true_nil.
Definition lists := native no_extension [("and", true_nil)].
Example list_reverse_keeps_duplicates : lists "eo::list_rev" [and_op; and_list [p; q; p]] = Some (and_list [p; q; p]).
Proof. reflexivity. Qed.
Example list_multiset_rejects_missing_duplicate : lists "eo::list_meq" [and_op; and_list [p; p]; and_list [p]] = Some (Symbol "false").
Proof. reflexivity. Qed.
Example list_multiset_accepts_permutation : lists "eo::list_meq" [and_op; and_list [p; p; q]; and_list [q; p; p]] = Some (Symbol "true").
Proof. reflexivity. Qed.
Example list_multiset_inclusion_direction : lists "eo::list_minclude" [and_op; and_list [p]; and_list [p; p]] = Some (Symbol "false").
Proof. reflexivity. Qed.
Example list_erases_one_occurrence : lists "eo::list_erase" [and_op; and_list [p; p]; p] = Some (and_list [p]).
Proof. reflexivity. Qed.
Example list_difference_consumes_occurrences : lists "eo::list_diff" [and_op; and_list [p; q; p]; and_list [p]] = Some (and_list [q; p]).
Proof. reflexivity. Qed.
Example list_intersection_consumes_occurrences : lists "eo::list_inter" [and_op; and_list [p; q; p]; and_list [p]] = Some (and_list [p]).
Proof. reflexivity. Qed.
Example list_nth_out_of_bounds : lists "eo::list_nth" [and_op; and_list [p]; Symbol "1"] = None.
Proof. reflexivity. Qed.
Example list_nth_negative : lists "eo::list_nth" [and_op; and_list [p]; Symbol "-1"] = None.
Proof. reflexivity. Qed.
Example list_nth_empty_index : lists "eo::list_nth" [and_op; and_list [p]; Symbol ""] = None.
Proof. reflexivity. Qed.
Example list_wrong_operator : lists "eo::list_rev" [and_op; binary "or" p true_nil] = None.
Proof. reflexivity. Qed.
Example list_missing_nil : lists "eo::list_rev" [and_op; binary "and" p q] = None.
Proof. reflexivity. Qed.
Example list_singleton_needs_explicit_elimination : lists "eo::list_singleton_elim" [and_op; and_list [p]] = Some p.
Proof. reflexivity. Qed.
Example source_generated_boolean_equality : cpc "evaluate" [binary "=" (Symbol "true") (Symbol "false")] [] =
  Some (binary "=" (binary "=" (Symbol "true") (Symbol "false")) (Symbol "false")).
Proof. vm_compute. reflexivity. Qed.
Example unsupported_arithmetic_does_not_fall_through : cpc "evaluate" [binary "-" (Symbol "3") (Symbol "1")] [] = None.
Proof. vm_compute. reflexivity. Qed.
Example unsupported_dependent_nil_rejects_before_fallback : cpc "evaluate"
  [Apply (binary "+" (Symbol "1") (Symbol "2")) (Symbol "3")] [] = None.
Proof. vm_compute. reflexivity. Qed.
Example trans_requires_matching_endpoints : cpc "trans" [] [binary "=" x y; binary "=" x y] = None.
Proof. vm_compute. reflexivity. Qed.
Example nested_boolean_surface_roundtrip : surface_in 100 [("and", true_nil)] (binary "and" p (binary "and" p q)) =
  Some (and_list [p; and_list [p; q]]).
Proof. reflexivity. Qed.
Example nil_does_not_cross_surface_boundary :
  match surface_in 100 [("and", true_nil)] (binary "and" p q) with
  | Some t => surface_out 100 [("and", true_nil)] t
  | _ => None
  end = Some (binary "and" p q).
Proof. reflexivity. Qed.

Print Assumptions trans_requires_matching_endpoints.
Print Assumptions list_multiset_rejects_missing_duplicate.

Definition assuming := CpcGenerated.derive_assuming 100 query.
Definition test_assuming := TestGenerated.derive_assuming 100 query.
Example source_assumption_scope : assuming "scope" p [] [q] = Some (binary "=>" p q).
Proof. reflexivity. Qed.
Example assumption_required_by_source : cpc "scope" [] [q] = None.
Proof. reflexivity. Qed.
Example ordinary_rule_rejects_extra_assumption : assuming "refl" p [x] [] = None.
Proof. reflexivity. Qed.
Example unknown_assumption_rule_rejects : assuming "unknown" p [] [q] = None.
Proof. reflexivity. Qed.
Example assumption_is_checked_boolean : assuming "scope" x [] [q] = None.
Proof. reflexivity. Qed.
Example assumption_does_not_supply_premise : assuming "scope" p [] [] = None.
Proof. reflexivity. Qed.
Example extra_local_premise_rejects : assuming "scope" p [] [p; q] = None.
Proof. reflexivity. Qed.
Example generated_assumption_pattern_accepts :
  test_assuming "novel_assumption" (unary "not" p) [p] [q] = Some (binary "=>" p q).
Proof. reflexivity. Qed.
Example generated_assumption_pattern_rejects :
  test_assuming "novel_assumption" p [p] [q] = None.
Proof. reflexivity. Qed.
Example generated_assumption_repeated_variable_rejects :
  test_assuming "novel_assumption" (unary "not" p) [q] [q] = None.
Proof. reflexivity. Qed.
Example generated_assumption_guard_accepts :
  test_assuming "guarded_assumption" p [] [p] = Some p.
Proof. reflexivity. Qed.
Example generated_assumption_guard_rejects :
  test_assuming "guarded_assumption" p [] [q] = None.
Proof. reflexivity. Qed.
Example process_scope_remains_ordinary : cpc "process_scope" [q] [binary "=>" p q] = Some (binary "=>" p q).
Proof. reflexivity. Qed.
Example process_scope_false : cpc "process_scope" [Symbol "false"] [binary "=>" p (Symbol "false")] = Some (unary "not" p).
Proof. reflexivity. Qed.
Example process_scope_nested_flat_surface : cpc "process_scope" [Symbol "false"]
  [binary "=>" p (binary "=>" q (Symbol "false"))] = Some (unary "not" (binary "and" p q)).
Proof. vm_compute. reflexivity. Qed.
Example process_scope_wrong_inner_conclusion : cpc "process_scope" [p] [binary "=>" p q] = None.
Proof. reflexivity. Qed.
Example process_scope_rejects_extra_assumption : assuming "process_scope" p [q] [binary "=>" p q] = None.
Proof. reflexivity. Qed.
Print Assumptions generated_assumption_pattern_rejects.
Print Assumptions process_scope_nested_flat_surface.
