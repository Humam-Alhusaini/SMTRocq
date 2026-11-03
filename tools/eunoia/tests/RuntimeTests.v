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
  | Symbol "U" | Symbol "Int" => Some (Symbol "Type")
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
Example helper_type_conflict : cpc "symm" [] [binary "=" x (Symbol "z")] = None.
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
Example helper_output_type_checked : TestGenerated.derive 100
  (fun t => if term_eqb t (Symbol "true") then None else query t) "output_type" [p] [] = None.
Proof. reflexivity. Qed.

Print Assumptions helper_symmetry.
Print Assumptions side_condition_reject.
