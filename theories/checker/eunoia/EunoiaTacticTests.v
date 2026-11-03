(**************************************************************************)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2026                                          *)
(*     Distributed under the terms of the CeCILL-C licence (see LICENSE). *)
(**************************************************************************)

From Stdlib Require Import List String Bool Uint63.
From SMTCoq.utils Require Import PArray.
From SMTCoq.checker.fol Require Import State Terms.
From SMTCoq.checker Require Import MainChecker.
From SMTCoq.checker.eunoia Require Import
  EoSyntax EunoiaAdapter EunoiaChecker EunoiaLocal EunoiaTactic.

Import ListNotations.
Local Open Scope uint63_scope.
Local Open Scope array_scope.
Local Open Scope string_scope.

Module A := EunoiaAdapter.Examples.

Definition eqxx := EunoiaAdapter.app "=" [A.x; A.x].
Definition not_eqxx := EunoiaAdapter.app "not" [eqxx].
Definition pair (a b : clause_id) : resolution := (PArray.make 2 a).[1 <- b].

Definition refl_evidence := EunoiaLocal.Witness 3 [(0, [Lit.nlit 14])]
  [EunoiaLocal.Command (Checker_Ext.EqTr 1 (Lit.lit 14) []) [Lit.lit 14];
   EunoiaLocal.Command (Checker_Ext.Res 2 (pair 0 1)) []] 2.

Definition contra_evidence := EunoiaLocal.Witness 3
  [(0, [Lit.lit 14]); (1, [Lit.nlit 14])]
  [EunoiaLocal.Command (Checker_Ext.Res 2 (pair 0 1)) []] 2.

Definition refl_payload := EunoiaAdapter.Payload "refl" [A.x] [] eqxx [Lit.lit 14].
Definition contra_payload := EunoiaAdapter.Payload "contra" []
  [eqxx; not_eqxx] (Symbol "false") [].

Definition steps : EunoiaTactic.trace :=
  [@EunoiaChecker.Step EunoiaAdapter.rule_payload EunoiaLocal.witness
     1 [] refl_payload [Lit.lit 14] refl_evidence;
   @EunoiaChecker.Step EunoiaAdapter.rule_payload EunoiaLocal.witness
     2 [1; 0] contra_payload [] contra_evidence].

Definition check := EunoiaTactic.checker_b
  A.sorts A.funcs A.atoms A.forms A.names 40 4.
Definition roots : list (clause_id * C.t) := [(0, [Lit.nlit 14])].

(* These are generated-rule and semantic-gate computations, not solver output. *)
Example generated_reflexivity_goal :
  check (Lit.lit 14) true [not_eqxx] roots steps 2 = true.
Proof. vm_compute; reflexivity. Qed.

Example reflected_goal_correct :
  Lit.interp (EunoiaTactic.valuation A.sorts A.funcs A.atoms A.forms) (Lit.lit 14) = true.
Proof.
  eapply EunoiaTactic.checker_b_correct; exact generated_reflexivity_goal.
Qed.

Example wrong_goal_rejected :
  check (Lit.lit 2) true [not_eqxx] roots steps 2 = false.
Proof. vm_compute; reflexivity. Qed.

Example wrong_result_rejected :
  check (Lit.lit 14) false [not_eqxx] roots steps 2 = false.
Proof. vm_compute; reflexivity. Qed.

Example wrong_polarity_rejected :
  check (Lit.nlit 14) true [not_eqxx] roots steps 2 = false.
Proof. vm_compute; reflexivity. Qed.

Example missing_root_term_rejected :
  check (Lit.lit 14) true [] roots steps 2 = false.
Proof. vm_compute; reflexivity. Qed.

Example extra_root_term_rejected :
  check (Lit.lit 14) true [not_eqxx; Symbol "false"] roots steps 2 = false.
Proof. vm_compute; reflexivity. Qed.

Example injected_empty_root_rejected :
  check (Lit.lit 14) true [not_eqxx] [(0, [])] steps 2 = false.
Proof. vm_compute; reflexivity. Qed.

Example missing_refl_step_rejected :
  check (Lit.lit 14) true [not_eqxx] roots (tl steps) 2 = false.
Proof. vm_compute; reflexivity. Qed.

Example wrong_conflict_rejected :
  check (Lit.lit 14) true [not_eqxx] roots steps 1 = false.
Proof. vm_compute; reflexivity. Qed.

Example unused_bad_step_rejected :
  check (Lit.lit 14) true [not_eqxx] roots
    (List.app steps [@EunoiaChecker.Step EunoiaAdapter.rule_payload EunoiaLocal.witness
      3 [] (EunoiaAdapter.Payload "unknown" [] [] eqxx [Lit.lit 14])
      [Lit.lit 14] refl_evidence]) 2 = false.
Proof. vm_compute; reflexivity. Qed.

Example positive_iff_claim_rejected :
  EunoiaTactic.checker_eq A.sorts A.funcs A.atoms A.forms A.names
    40 4 (Lit.lit 14) (Lit.lit 14) (Lit.lit 14)
    [not_eqxx] roots steps 2 = false.
Proof. vm_compute; reflexivity. Qed.

Example nonequivalence_form_rejected :
  EunoiaTactic.checker_eq A.sorts A.funcs A.atoms A.forms A.names
    40 4 (Lit.lit 14) (Lit.lit 14) (Lit.nlit 14)
    [not_eqxx] roots steps 2 = false.
Proof. vm_compute; reflexivity. Qed.

Example changed_iff_children_rejected :
  EunoiaTactic.checker_eq A.sorts A.funcs A.atoms A.forms A.names
    40 4 (Lit.lit 6) (Lit.lit 5) (Lit.nlit 9)
    [not_eqxx] roots steps 2 = false.
Proof. vm_compute; reflexivity. Qed.
