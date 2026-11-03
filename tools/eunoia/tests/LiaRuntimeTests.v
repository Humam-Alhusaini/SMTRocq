From Stdlib Require Import String List Bool.
From SMTCoq.checker.eunoia Require Import EoSyntax EoRuntime EoOrder CpcGenerated LiaTraceReplay.
From SMTCoq.checker.eunoia Require LiaMutatedGenerated.
Import ListNotations.
Open Scope string_scope.
Definition s := Symbol.
Definition u op a := Apply (s op) a.
Definition b op a c := Apply (u op a) c.
Definition n op xs := apply_many (s op) xs.
Definition x := s "x".
Definition y := s "y".
Definition q := lia_query [("x", s "Int"); ("y", s "Int"); ("p", s "Bool")].
Definition run := derive 500 q.
Definition eq := b "=".
Definition diff := b "-".
Definition scaled c a d := b "*" (s c) (diff a d).
Definition relations op := eq (b op x (s "0")) (b op y (s "1")).
Definition relation_premise c d := eq (scaled c x (s "0")) (scaled d y (s "1")).

Example integer_dependent_nil :
  let nilof := resolve_nil default_primitive cpc_operators 100 q cpc_programs cpc_nils in
  nilof "+" (Some (s "Int")) = Some (s "0") /\ nilof "*" (Some (s "Int")) = Some (s "1").
Proof. vm_compute. split; reflexivity. Qed.
Example rational_dependent_nil :
  let nilof := resolve_nil default_primitive cpc_operators 100 q cpc_programs cpc_nils in
  nilof "+" (Some (s "Real")) = Some (s "0/1") /\ nilof "*" (Some (s "Real")) = Some (s "1/1").
Proof. vm_compute. split; reflexivity. Qed.
Example typed_list_nil :
  let nilof := resolve_nil default_primitive cpc_operators 100 q cpc_programs cpc_nils in
  nilof "@@TypedList.cons" (Some (s "Int")) = Some (Apply (s "@@TypedList.nil") (s "Int")).
Proof. vm_compute. reflexivity. Qed.
Example unknown_nil_type_rejects :
  let nilof := resolve_nil default_primitive cpc_operators 100 q cpc_programs cpc_nils in
  surface_in_with nilof q 100 cpc_operators (b "+" (s "p") (s "p")) = None.
Proof. vm_compute. reflexivity. Qed.
Example production_arithmetic_default : run "evaluate" [n "+" [s "8"; s "-11"; s "3"]] [] =
  Some (eq (n "+" [s "8"; s "-11"; s "3"]) (s "0")).
Proof. vm_compute. reflexivity. Qed.
Example overloaded_unary_minus : run "evaluate" [u "-" (s "3")] [] = Some (eq (u "-" (s "3")) (s "-3")).
Proof. vm_compute. reflexivity. Qed.
Example overloaded_binary_minus : run "evaluate" [b "-" (s "3") (s "1")] [] = Some (eq (b "-" (s "3") (s "1")) (s "2")).
Proof. vm_compute. reflexivity. Qed.
Example polynomial_commutes : run "arith_poly_norm" [eq (b "+" x y) (b "+" y x)] [] = Some (eq (b "+" x y) (b "+" y x)).
Proof. vm_compute. reflexivity. Qed.
Example monomial_commutes : run "arith_poly_norm" [eq (b "*" x y) (b "*" y x)] [] = Some (eq (b "*" x y) (b "*" y x)).
Proof. vm_compute. reflexivity. Qed.
Example invalid_coefficient_rejects : run "arith_poly_norm" [eq (b "*" (s "2") x) (b "*" (s "3") x)] [] = None.
Proof. vm_compute. reflexivity. Qed.
Example zero_relation_coefficient_rejects : run "arith_poly_norm_rel" [relations "<"] [relation_premise "0" "1"] = None.
Proof. vm_compute. reflexivity. Qed.
Example opposite_relation_signs_reject : run "arith_poly_norm_rel" [relations "<"] [relation_premise "1" "-1"] = None.
Proof. vm_compute. reflexivity. Qed.
Example equality_allows_opposite_signs : run "arith_poly_norm_rel" [relations "="] [relation_premise "1" "-1"] = Some (relations "=").
Proof. vm_compute. reflexivity. Qed.
Example changed_relation_endpoint_rejects :
  run "arith_poly_norm_rel" [relations "<"] [eq (scaled "1" x (s "2")) (scaled "1" y (s "1"))] = None.
Proof. vm_compute. reflexivity. Qed.
Example changed_multiplication_tail_rejects :
  run "arith_poly_norm_rel" [relations "<"] [eq (n "*" [s "1"; diff x (s "0"); s "2"]) (n "*" [s "1"; diff y (s "1"); s "2"])] = None.
Proof. vm_compute. reflexivity. Qed.
Example extra_premise_rejects : run "arith_poly_norm_rel" [relations "<"] [relation_premise "1" "1"; relation_premise "1" "1"] = None.
Proof. vm_compute. reflexivity. Qed.
Example scaling_retains_exact_guard : run "arith_mult_neg" [s "-1"; b "<=" x y] [] =
  Some (b "=>" (b "and" (b "<" (s "-1") (s "0")) (b "<=" x y))
    (b ">=" (b "*" (s "-1") x) (b "*" (s "-1") y))).
Proof. vm_compute. reflexivity. Qed.
Example positive_scaling_still_retains_negative_guard : run "arith_mult_neg" [s "1"; b "<=" x y] [] =
  Some (b "=>" (b "and" (b "<" (s "1") (s "0")) (b "<=" x y))
    (b ">=" (b "*" (s "1") x) (b "*" (s "1") y))).
Proof. vm_compute. reflexivity. Qed.
Example invalid_scaling_relation_rejects : run "arith_mult_neg" [s "-1"; s "p"] [] = None.
Proof. vm_compute. reflexivity. Qed.
Example sum_order_and_multiplicity : run "arith_sum_ub" [] [b "<=" x (s "1"); b "<" y (s "2"); b "<=" x (s "1")] =
  Some (b "<" (n "+" [x; y; x]) (n "+" [s "1"; s "2"; s "1"])).
Proof. vm_compute. reflexivity. Qed.
Example equality_plus_equality_is_leq : run "arith_sum_ub" [] [eq x (s "1"); eq y (s "2")] =
  Some (b "<=" (b "+" x y) (b "+" (s "1") (s "2"))).
Proof. vm_compute. reflexivity. Qed.
Example empty_sum_rejects : run "arith_sum_ub" [] [] = None.
Proof. vm_compute. reflexivity. Qed.
Example invalid_sum_relation_rejects : run "arith_sum_ub" [] [b ">=" x y] = None.
Proof. vm_compute. reflexivity. Qed.
Example tightening_endpoint : run "int_tight_ub" [] [b "<" x (s "-3")] = Some (b "<=" x (s "-4")).
Proof. vm_compute. reflexivity. Qed.
Example nonstrict_tightening_rejects : run "int_tight_ub" [] [b "<=" x (s "3")] = None.
Proof. vm_compute. reflexivity. Qed.
Example missing_conversion_is_diagnostic : evaluate_computation (closed_nil []) no_extension [] 100 q [] []
  (ENative "eo::is_q" [ENative "eo::to_q" [ESymbol "x"]]) = Missing "eo::to_q".
Proof. vm_compute. reflexivity. Qed.
Example available_stuck_conversion_is_observable : evaluate_computation (closed_nil []) default_primitive [] 100 q [] []
  (ENative "eo::is_q" [ENative "eo::to_q" [ESymbol "x"]]) = Done (s "false").
Proof. vm_compute. reflexivity. Qed.
Example is_ok_cannot_hide_missing_primitive : evaluate_with no_extension [] 100 q [] []
  (EIsOk (ENative "eo::to_q" [ESymbol "x"])) = None.
Proof. vm_compute. reflexivity. Qed.
Example missing_primitive_cannot_select_polynomial_fallback : derive_with no_extension 500 q "arith_poly_norm" [eq x x] [] = None.
Proof. vm_compute. reflexivity. Qed.
Example supplied_typequery_is_required : derive 500 (fun _ => None) "arith_poly_norm" [eq x x] [] = None.
Proof. vm_compute. reflexivity. Qed.
Example boolean_impl_true2 : run "bool-impl-true2" [s "p"] [] = Some (eq (b "=>" (s "true") (s "p")) (s "p")).
Proof. vm_compute. reflexivity. Qed.
Example order_distinguishes_structure : EoOrder.eval [b "+" x y; b "+" x x] = Some (s "true").
Proof. vm_compute. reflexivity. Qed.

Print Assumptions integer_dependent_nil.
Print Assumptions rational_dependent_nil.
Print Assumptions typed_list_nil.
Print Assumptions unknown_nil_type_rejects.
Print Assumptions production_arithmetic_default.
Print Assumptions overloaded_unary_minus.
Print Assumptions overloaded_binary_minus.
Print Assumptions polynomial_commutes.
Print Assumptions monomial_commutes.
Print Assumptions invalid_coefficient_rejects.
Print Assumptions zero_relation_coefficient_rejects.
Print Assumptions opposite_relation_signs_reject.
Print Assumptions equality_allows_opposite_signs.
Print Assumptions changed_relation_endpoint_rejects.
Print Assumptions changed_multiplication_tail_rejects.
Print Assumptions extra_premise_rejects.
Print Assumptions scaling_retains_exact_guard.
Print Assumptions positive_scaling_still_retains_negative_guard.
Print Assumptions invalid_scaling_relation_rejects.
Print Assumptions sum_order_and_multiplicity.
Print Assumptions equality_plus_equality_is_leq.
Print Assumptions empty_sum_rejects.
Print Assumptions invalid_sum_relation_rejects.
Print Assumptions tightening_endpoint.
Print Assumptions nonstrict_tightening_rejects.
Print Assumptions missing_conversion_is_diagnostic.
Print Assumptions available_stuck_conversion_is_observable.
Print Assumptions is_ok_cannot_hide_missing_primitive.
Print Assumptions missing_primitive_cannot_select_polynomial_fallback.
Print Assumptions supplied_typequery_is_required.
Print Assumptions boolean_impl_true2.
Print Assumptions order_distinguishes_structure.

Example source_relation_table_mutation_changes_computation :
  LiaMutatedGenerated.derive 500 q "arith_sum_ub" [] [eq x (s "1"); eq y (s "2")] =
  Some (eq (b "+" x y) (b "+" (s "1") (s "2"))).
Proof. vm_compute. reflexivity. Qed.
Print Assumptions source_relation_table_mutation_changes_computation.

Definition typed_list_query t :=
  match t with
  | Apply (Symbol "@@TypedList.nil") (Symbol "Int") =>
      Some (Apply (s "@@TypedList") (s "Int"))
  | _ => q t end.
Example typed_list_nil_matches_tail_type :
  let nilof := resolve_nil default_primitive cpc_operators 100 typed_list_query cpc_programs cpc_nils in
  match_pattern_with nilof typed_list_query (PNil "@@TypedList.cons")
    (Apply (s "@@TypedList.nil") (s "Int")) [] = Some [].
Proof. vm_compute. reflexivity. Qed.
Example native_nil_uses_tail_type :
  let nilof := resolve_nil default_primitive cpc_operators 100 typed_list_query cpc_programs cpc_nils in
  native_with_nils nilof typed_list_query default_primitive cpc_operators "eo::nil"
    [s "@@TypedList.cons"; Apply (s "@@TypedList") (s "Int")] =
  Some (Apply (s "@@TypedList.nil") (s "Int")).
Proof. vm_compute. reflexivity. Qed.
Print Assumptions typed_list_nil_matches_tail_type.
Print Assumptions native_nil_uses_tail_type.

Example empty_typed_list_reverse_keeps_parameter :
  let nilof := resolve_nil default_primitive cpc_operators 100 typed_list_query cpc_programs cpc_nils in
  native_with_nils nilof typed_list_query default_primitive cpc_operators "eo::list_rev"
    [s "@@TypedList.cons"; Apply (s "@@TypedList.nil") (s "Int")] =
  Some (Apply (s "@@TypedList.nil") (s "Int")).
Proof. vm_compute. reflexivity. Qed.
Example zero_typed_list_repeat_uses_element_type :
  let nilof := resolve_nil default_primitive cpc_operators 100 q cpc_programs cpc_nils in
  native_with_nils nilof q default_primitive cpc_operators "eo::list_repeat"
    [s "@@TypedList.cons"; x; s "0"] = Some (Apply (s "@@TypedList.nil") (s "Int")).
Proof. vm_compute. reflexivity. Qed.
Print Assumptions empty_typed_list_reverse_keeps_parameter.
Print Assumptions zero_typed_list_repeat_uses_element_type.
