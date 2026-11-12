(**************************************************************************)
(*     SMTCoq -- distributed under the terms of the CeCILL-C licence       *)
(**************************************************************************)

From Stdlib Require Import List String Bool Uint63.
From SMTCoq.utils Require Import PArray.
From SMTCoq.checker.fol Require Import State Terms.
From SMTCoq.checker Require Import MainChecker.
From SMTCoq.checker.eunoia Require Import
  EoSyntax EunoiaChecker EunoiaBridge EunoiaAdapter EunoiaLocal.

Import ListNotations.
Local Open Scope uint63_scope.
Local Open Scope array_scope.
Local Open Scope string_scope.
Module A := EunoiaAdapter.
Module B := EunoiaBridge.
Module L := EunoiaLocal.
Module K := EunoiaChecker.

Definition ti := A.Examples.sorts.
Definition tf := A.Examples.funcs.
Definition ta := A.Examples.atoms.
Definition fm := (PArray.make 3 Form.Ftrue).[1 <- Form.Ffalse]
  .[2 <- Form.Fiff 0 0].
Definition ns := A.Examples.names.
Definition weak := Checker_Ext.Weaken 1 0 [0].

(* [4] cannot be weakened to [0], even though [0] is a valid tautology. *)
Example failed_weakening_rejected :
  @B.gate ti tf ta fm [[4]] [0] (B.Witness 2 weak) = false.
Proof. vm_compute; reflexivity. Qed.

Example identity_weakening_accepts :
  @B.gate ti tf ta fm [[4]] [4]
    (B.Witness 2 (Checker_Ext.Weaken 1 0 [4])) = true.
Proof. vm_compute; reflexivity. Qed.

Example dedicated_true_accepts :
  @B.gate ti tf ta fm [] [0] (B.Witness 1 (Checker_Ext.CTrue 0)) = true.
Proof. vm_compute; reflexivity. Qed.

Example equality_failure_cannot_certify_true :
  @B.gate ti tf ta fm [] [0] (B.Witness 1 (Checker_Ext.EqTr 0 2 [])) = false.
Proof. vm_compute; reflexivity. Qed.

Example production_gate_rejects_same_failed_weakening :
  @L.execute ti tf ta fm (L.Machine (S.set_clause (S.make 2) 0 [4]) [0])
    (L.Command weak [0]) = None.
Proof. vm_compute; reflexivity. Qed.

Definition res2 := (PArray.make 2 0).[1 <- 1].
Definition p1 := A.Payload "true_elim" [] [A.app "=" [Symbol "true";Symbol "true"]]
  (Symbol "true") [0].
Definition p2 := A.Payload "contra" [] [Symbol "true";A.app "not" [Symbol "true"]]
  (Symbol "false") [].

(* The real generated adapter must reject the malformed semantic witness too. *)
Example concrete_adapter_rejects_failed_witness :
  @A.checked_checker ti tf ta fm ns 100 4 [[4];[1]]
    [A.app "=" [Symbol "true";Symbol "true"];A.app "not" [Symbol "true"]]
    [(0,[4]);(1,[1])]
    [K.Step 2 [0] p1 [0] (B.Witness 2 weak);
     K.Step 3 [2;1] p2 [] (B.Witness 3 (Checker_Ext.Res 2 res2))] 3 = false.
Proof. vm_compute; reflexivity. Qed.

Definition res4 := ((PArray.make 4 0).[1 <- 1]).[2 <- 2].[3 <- 3].
Example failed_intermediate_resolution_link_rejected :
  @B.gate ti tf ta fm [[0];[0];[1];[1]] []
    (B.Witness 5 (Checker_Ext.Res 4 res4)) = false.
Proof. vm_compute; reflexivity. Qed.

Example binary_resolution_accepts :
  @B.gate ti tf ta fm [[4];[5]] []
    (B.Witness 3 (Checker_Ext.Res 2 res2)) = true.
Proof. vm_compute; reflexivity. Qed.

Example single_entry_resolution_rejected :
  @B.gate ti tf ta fm [[4]] [4]
    (B.Witness 2 (Checker_Ext.Res 1 (PArray.make 1 0))) = false.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions concrete_adapter_rejects_failed_witness.
Print Assumptions binary_resolution_accepts.
