(* Typed metadata, exact lowering, and rejection controls for integer cuts. *)
From Stdlib Require Import List String Bool ZArith Uint63.
From SMTCoq.checker.eunoia Require Import EoSyntax CpcGenerated EunoiaIntegerEmbedding EunoiaAdapter.
Import ListNotations.
Local Open Scope string_scope.
Module A := EunoiaAdapter.Examples.
Definition app := EunoiaAdapter.app.
Definition query := EunoiaAdapter.typeof A.sorts A.funcs A.names 100.
Definition normalize := EunoiaAdapter.normalize_source A.sorts A.funcs A.names 100.
Definition n := Symbol "n".
Example cast_integer_type : query (app "to_real" [n]) = Some (Symbol "Real").
Proof. vm_compute; reflexivity. Qed.
Example cast_floor_type : query (app "to_int" [Symbol "-3/2"]) = Some (Symbol "Int").
Proof. vm_compute; reflexivity. Qed.
Example floor_arithmetic_type : query (app "+" [app "to_int" [Symbol "-3/2"];Symbol "1"]) = Some (Symbol "Int").
Proof. vm_compute; reflexivity. Qed.
Example rational_arithmetic_type :
  query (app "*" [Symbol "3/2";app "to_real" [n]]) = Some (Symbol "Real").
Proof. vm_compute; reflexivity. Qed.
Example rational_relation_type :
  query (app ">=" [app "to_real" [n];Symbol "-3/2"]) = Some (Symbol "Bool").
Proof. vm_compute; reflexivity. Qed.
Example nested_rational_formula_type :
  query (app "not" [app "=" [app "to_real" [n];Symbol "1/2"]]) = Some (Symbol "Bool").
Proof. vm_compute; reflexivity. Qed.
Example integer_to_real_wrong_sort : query (app "to_real" [A.p]) = None.
Proof. vm_compute; reflexivity. Qed.
Example real_to_integer_wrong_sort : query (app "to_int" [n]) = None.
Proof. vm_compute; reflexivity. Qed.
Example cast_wrong_arity : query (app "to_real" [n;n]) = None.
Proof. vm_compute; reflexivity. Qed.
Example mixed_arithmetic_rejected : query (app "+" [n;Symbol "1/2"]) = None.
Proof. vm_compute; reflexivity. Qed.
Example unknown_real_rejected : query (app "to_int" [Symbol "unknown-real"]) = None.
Proof. vm_compute; reflexivity. Qed.
Example fractional_equality :
  normalize (app "=" [app "to_real" [n];Symbol "1/2"]) =
    Some (app "=" [app "*" [Symbol "2";n];Symbol "1"]).
Proof. vm_compute; reflexivity. Qed.
Example negative_fractional_bound :
  normalize (app ">=" [app "to_real" [n];Symbol "-3/2"]) =
    Some (app ">=" [app "*" [Symbol "2";n];Symbol "-3"]).
Proof. vm_compute; reflexivity. Qed.
Example negative_floor_exact : normalize (app "to_int" [Symbol "-3/2"]) = Some (Symbol "-2").
Proof. vm_compute; reflexivity. Qed.
Example negative_floor_not_truncation : normalize (app "to_int" [Symbol "-3/2"]) <> Some (Symbol "-1").
Proof. vm_compute; discriminate. Qed.
Example integral_round_trip :
  normalize (app "to_int" [app "to_real" [n]]) = Some n.
Proof. vm_compute; reflexivity. Qed.
Example fractional_non_ground_floor_rejected :
  normalize (app "to_int" [app "*" [Symbol "1/2";app "to_real" [n]]]) = None.
Proof. vm_compute; reflexivity. Qed.
Example zero_division_rejected : normalize (app "=" [app "/" [Symbol "1/1";Symbol "0/1"];Symbol "1/1"]) = None.
Proof. vm_compute; reflexivity. Qed.
Example changed_denominator_changes_binding :
  normalize (app "=" [app "to_real" [n];Symbol "1/3"]) <>
    Some (app "=" [app "*" [Symbol "2";n];Symbol "1"]).
Proof. vm_compute; discriminate. Qed.
Example ordinary_integer_shape_preserved :
  normalize (app "+" [n;Symbol "1";n]) = Some (app "+" [n;app "+" [Symbol "1";n]]).
Proof. vm_compute; reflexivity. Qed.
Example zero_fuel_rejected :
  EunoiaAdapter.normalize_source A.sorts A.funcs A.names 0
    (app "=" [app "to_real" [n];Symbol "1/2"]) = None.
Proof. vm_compute; reflexivity. Qed.
Example cast_name_shadowing_rejected :
  EunoiaAdapter.names_wf A.sorts A.funcs (EunoiaAdapter.Naming [] [(0%uint63,"to_real")]) = false.
Proof. vm_compute; reflexivity. Qed.

Example generated_trichotomy :
  CpcGenerated.derive 1000 query "arith_trichotomy" []
    [app ">=" [n;Symbol "1"];app "<=" [n;Symbol "1"]] = Some (app "=" [n;Symbol "1"]).
Proof. vm_compute; reflexivity. Qed.
Example trichotomy_changed_endpoint_rejected :
  CpcGenerated.derive 1000 query "arith_trichotomy" []
    [app ">=" [n;Symbol "1"];app "<=" [n;Symbol "2"]] = None.
Proof. vm_compute; reflexivity. Qed.
Example trichotomy_missing_premise_rejected :
  CpcGenerated.derive 1000 query "arith_trichotomy" [] [app ">=" [n;Symbol "1"]] = None.
Proof. vm_compute; reflexivity. Qed.

Example generated_positive_scale :
 CpcGenerated.derive 1000 query "arith_mult_pos" [Symbol "3";app "<=" [n;Symbol "1"]] [] =
 Some (app "=>" [app "and" [app ">" [Symbol "3";Symbol "0"];app "<=" [n;Symbol "1"]];
  app "<=" [app "*" [Symbol "3";n];app "*" [Symbol "3";Symbol "1"]]]).
Proof. vm_compute; reflexivity. Qed.
Example positive_scale_wrong_sort :
 CpcGenerated.derive 1000 query "arith_mult_pos" [Symbol "true";app "<=" [n;Symbol "1"]] [] = None.
Proof. vm_compute; reflexivity. Qed.
Example positive_scale_wrong_arity :
 CpcGenerated.derive 1000 query "arith_mult_pos" [Symbol "3"] [] = None.
Proof. vm_compute; reflexivity. Qed.

Example generated_lower_tightening :
 CpcGenerated.derive 1000 query "int_tight_lb" [] [app ">" [n;Symbol "-2"]] =
 Some (app ">=" [n;Symbol "-1"]).
Proof. vm_compute; reflexivity. Qed.
Example lower_tightening_wrong_relation :
 CpcGenerated.derive 1000 query "int_tight_lb" [] [app ">=" [n;Symbol "-2"]] = None.
Proof. vm_compute; reflexivity. Qed.
Example lower_tightening_missing_premise :
 CpcGenerated.derive 1000 query "int_tight_lb" [] [] = None.
Proof. vm_compute; reflexivity. Qed.
