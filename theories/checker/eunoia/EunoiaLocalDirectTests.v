(* SMTCoq -- distributed under the CeCILL-C licence (see LICENSE). *)
From Stdlib Require Import List Bool String Uint63.
From SMTCoq.checker.fol Require Import State Terms.
From SMTCoq.checker Require Import MainChecker.
From SMTCoq.checker.eunoia Require Import EunoiaLocal EunoiaLocalDirect
 EunoiaMemo EunoiaMemoTests EunoiaScope EunoiaAdapter.
Import ListNotations.
Local Open Scope uint63_scope.
Local Open Scope string_scope.
Module EunoiaLocalDirectTests.
Module T := EunoiaMemoTests.
Module S := T.S.
Module L := EunoiaLocal.
Definition gate := @EunoiaLocalDirect.gate S.sorts S.funcs S.atoms S.forms.
Definition identity := L.Witness 1 [(0,[4])] [] 0.
Example exact_premise_derives_itself : gate [[4]] [4] identity = true.
Proof. vm_compute; reflexivity. Qed.
Example altered_conclusion_rejected : gate [[4]] [5] identity = false.
Proof. vm_compute; reflexivity. Qed.
Example missing_premise_rejected : gate [] [4] identity = false.
Proof. vm_compute; reflexivity. Qed.
Example extra_premise_must_be_claimed : gate [[4];[5]] [4] identity = false.
Proof. vm_compute; reflexivity. Qed.
Definition truth := L.Witness 1 [] [L.Command (Checker_Ext.CTrue 0) [0]] 0.
Example explicit_truth_derivation : gate [] [0] truth = true.
Proof. vm_compute; reflexivity. Qed.
Example invalid_unused_command_rejected :
 gate [] [0] (L.Witness 2 []
  [L.Command (Checker_Ext.CTrue 0) [0]; L.Command (Checker_Ext.CTrue 1) []] 0) = false.
Proof. vm_compute; reflexivity. Qed.
Example invalid_true_fallback_rejected :
 gate [] [0] (L.Witness 1 [] [L.Command (Checker_Ext.EqTr 0 4 []) [0]] 0) = false.
Proof. vm_compute; reflexivity. Qed.
Example out_of_bounds_result_rejected : gate [[4]] [4] (L.Witness 1 [(0,[4])] [] 5) = false.
Proof. vm_compute; reflexivity. Qed.
Definition direct_body := EunoiaScope.Next
 (T.step 3 [2;1] S.contra_p [] (EunoiaMemo.Direct (S.contradiction 4))) T.done.
Definition mixed := EunoiaScope.Push 2 4 direct_body (Some T.closing) T.finish.
Example complete_generated_source_checker_accepts : T.check T.entries mixed = true.
Proof. vm_compute; reflexivity. Qed.
Definition unsupported := EunoiaAdapter.Payload "unsupported" [] [S.p; S.neg S.p] S.f [].
Definition bad_finish := EunoiaScope.Next (T.step 5 [4] S.process_p [5] (EunoiaMemo.Cached 2))
 (EunoiaScope.Next (T.step 6 [0;5] S.contra_p [] (EunoiaMemo.Direct (S.contradiction 4)))
  (EunoiaScope.Next (T.step 7 [0;5] unsupported [] (EunoiaMemo.Direct (S.contradiction 4))) T.done)).
Example bad_source_after_conflict_rejected :
 T.check T.entries (EunoiaScope.Push 2 4 direct_body (Some T.closing) bad_finish) = false.
Proof. vm_compute; reflexivity. Qed.
Example direct_refutation_is_sound : ~ Forall (C.valid S.rho) S.roots.
Proof. eapply EunoiaMemo.checker_correct; exact complete_generated_source_checker_accepts. Qed.
Print Assumptions direct_refutation_is_sound.
End EunoiaLocalDirectTests.
