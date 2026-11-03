(**************************************************************************)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2026                                          *)
(*     Distributed under the terms of the CeCILL-C licence (see LICENSE). *)
(**************************************************************************)

From Stdlib Require Import List Bool Uint63.
From SMTCoq.utils Require Import PArray.
From SMTCoq.checker.fol Require Import State Terms.
From SMTCoq.checker Require Import MainChecker.
From SMTCoq.checker.eunoia Require Import EunoiaChecker EunoiaBridge.

Import ListNotations EunoiaChecker.
Local Open Scope uint63_scope.
Local Open Scope array_scope.

(* An intentionally untrusted test evaluator. These are not CPC rules. The
   Return case tests that even an arbitrary claimed result cannot bypass the
   real semantic gate. No test evaluator is exported as a sound CPC adapter. *)
Module EunoiaCheckerTests.
Inductive test_rule := ResolvePair | Return (c : C.t) | Unknown.

Definition test_eval (r : test_rule) (cs : list C.t) : option C.t :=
  match r with
  | ResolvePair => if EunoiaBridge.clauses_eqb cs [[4]; [5]] then Some [] else None
  | Return c => Some c
  | Unknown => None
  end.

Definition res_ids : resolution := (PArray.make 2 0).[1 <- 1].
Definition res_witness := EunoiaBridge.Witness 3 (Checker_Ext.Res 2 res_ids).
Definition good_step := Step 2 [0; 1] ResolvePair [] res_witness.
Definition unknown_step := Step 3 [] Unknown [] res_witness.
Definition roots : list C.t := [[4]; [5]].
Definition claims : list (clause_id * C.t) := [(0, [4]); (1, [5])].
Definition forms : array Form.form := PArray.make 4 Form.Ftrue.

Section Context.
  Variable t_i : array CompDec.typ_compdec.
  Variable t_func : array (Atom.tval t_i).
  Variable t_atom : array Atom.atom.

  Local Definition gate := @EunoiaBridge.gate t_i t_func t_atom forms.
  Local Definition check := EunoiaChecker.checker test_eval gate 4.

  Example resolution_accepts : check 4 roots claims [good_step] 2 = true.
  Proof. vm_compute; reflexivity. Qed.

  Example exact_premise_order_required :
    check 4 roots claims [Step 2 [1; 0] ResolvePair [] res_witness] 2 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example unknown_rejected : check 4 roots claims [unknown_step] 2 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example unknown_before_conflict_rejected :
    check 4 roots claims [unknown_step; good_step] 2 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example unknown_after_conflict_rejected :
    check 4 roots claims [good_step; unknown_step] 2 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example uninitialized_premise_rejected :
    check 4 roots claims [Step 2 [0; 3] (Return []) [] res_witness] 2 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example out_of_bounds_premise_rejected :
    check 3 roots claims [Step 2 [0; 3] (Return []) [] res_witness] 2 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example forward_premise_rejected :
    check 4 roots claims [Step 2 [0; 2] (Return []) [] res_witness] 2 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example overwritten_root_rejected :
    check 4 roots claims [Step 0 [0; 1] ResolvePair [] res_witness] 0 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example duplicate_step_rejected :
    check 4 roots claims [good_step; good_step] 2 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example out_of_bounds_destination_rejected :
    check 2 roots claims [good_step] 2 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example evaluator_conclusion_mismatch_rejected :
    check 4 roots claims [Step 2 [0; 1] ResolvePair [4] res_witness] 2 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example witness_conclusion_mismatch_rejected :
    check 4 roots claims
      [Step 2 [0] (Return []) []
        (EunoiaBridge.Witness 3 (Checker_Ext.Weaken 2 0 [4]))] 2 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example unrelated_tautology_cannot_witness_conflict :
    check 4 roots claims
      [Step 2 [] (Return []) []
        (EunoiaBridge.Witness 3 (Checker_Ext.CTrue 2))] 2 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example changed_root_rejected :
    check 4 roots [(0, [4]); (1, [4])] [good_step] 2 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example reordered_roots_rejected :
    check 4 roots [(0, [5]); (1, [4])] [good_step] 2 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example missing_root_rejected :
    check 4 roots [(0, [4])] [good_step] 2 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example extra_root_rejected :
    check 4 roots (claims ++ [(3, [])]) [good_step] 2 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example duplicate_root_slot_rejected :
    check 4 roots [(0, [4]); (0, [5])] [good_step] 2 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example out_of_bounds_root_rejected :
    check 4 roots [(0, [4]); (4, [5])] [good_step] 2 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example wrong_goal_rejected : check 4 roots claims [good_step] 0 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example uninitialized_goal_rejected : check 4 roots claims [good_step] 3 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example out_of_bounds_goal_rejected : check 4 roots claims [good_step] 4 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example missing_witness_premise_rejected :
    gate [[4]] [] res_witness = false.
  Proof. vm_compute; reflexivity. Qed.

  Example extra_witness_premise_rejected :
    gate (roots ++ [[4]]) [] res_witness = false.
  Proof. vm_compute; reflexivity. Qed.

  Example incorrect_witness_premises_rejected :
    gate [[4]; [4]] [] res_witness = false.
  Proof. vm_compute; reflexivity. Qed.

  Example witness_cannot_hide_extra_reads_via_combine :
    gate [[4]; [5]] []
      (EunoiaBridge.Witness 4
        (Checker_Ext.Res 3 ((PArray.make 3 0).[1 <- 1]))) = false.
  Proof. vm_compute; reflexivity. Qed.

  Example witness_output_overwrite_rejected :
    gate roots [] (EunoiaBridge.Witness 3 (Checker_Ext.Res 0 res_ids)) = false.
  Proof. vm_compute; reflexivity. Qed.

  Example witness_output_out_of_bounds_rejected :
    gate roots [] (EunoiaBridge.Witness 2 (Checker_Ext.Res 2 res_ids)) = false.
  Proof. vm_compute; reflexivity. Qed.

  Example empty_resolution_rejected :
    gate [] C._true
      (EunoiaBridge.Witness 1 (Checker_Ext.Res 0 (PArray.make 0 0))) = false.
  Proof. vm_compute; reflexivity. Qed.

  Example unsupported_witness_rejected :
    gate [] [] (EunoiaBridge.Witness 1 (Checker_Ext.BBVar 0 4)) = false.
  Proof. vm_compute; reflexivity. Qed.
  Example invalid_formula_table_rejected :
    @EunoiaBridge.checker t_i t_func t_atom forms test_rule
      test_eval 4 roots claims [good_step] 2 = false.
  Proof. vm_compute; reflexivity. Qed.
End Context.

Example malformed_literal_rejected : store 4 (initial 1) 0 [8] = None.
Proof. vm_compute; reflexivity. Qed.

Example noncanonical_conclusion_rejected : store 4 (initial 1) 0 [5; 4] = None.
Proof. vm_compute; reflexivity. Qed.

Example malformed_root_rejected :
  load_roots 4 (initial 1) [[8]] [(0, [8])] = None.
Proof. vm_compute; reflexivity. Qed.

End EunoiaCheckerTests.
