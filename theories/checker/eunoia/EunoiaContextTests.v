(**************************************************************************)
(* SMTCoq -- distributed under the terms of the CeCILL-C licence           *)
(**************************************************************************)
From Stdlib Require Import List String Bool Uint63.
From SMTCoq.utils Require Import PArray.
From SMTCoq.checker.fol Require Import State Terms.
From SMTCoq.checker Require Import MainChecker.
From SMTCoq.checker.eunoia Require Import
  EoSyntax EunoiaChecker EunoiaAdapter EunoiaLocal EunoiaTactic EunoiaScope
  EunoiaScopedAdapter EunoiaScopedAdapterTests EunoiaTacticTests.
Import ListNotations.
Local Open Scope uint63_scope.
Local Open Scope array_scope.
Local Open Scope string_scope.

Module EunoiaContextTests.
Module F := EunoiaScopedAdapterTests.EunoiaScopedAdapterTests.

(* These use the concrete generated-rule / local-command gates. The fixtures
   contain checked nested scopes, not an abstract always-accepting callback. *)
Example scoped_positive : F.check_single F.single 6 = true.
Proof. vm_compute; reflexivity. Qed.
Example nested_positive : F.check_nested F.nested 8 = true.
Proof. vm_compute; reflexivity. Qed.

Definition duplicate_names := EunoiaAdapter.Naming [] [(0,"p"); (1,"p")].
Example malformed_names_rejected :
  @EunoiaScopedAdapter.checker F.sorts F.funcs F.atoms F.forms duplicate_names
    100 12 F.roots F.root_terms F.claims F.single 6 = false.
Proof. vm_compute; reflexivity. Qed.
Example illtyped_tables_rejected :
  @EunoiaScopedAdapter.checker F.sorts F.funcs F.bad_atoms F.forms F.names
    100 12 F.roots F.root_terms F.claims F.single 6 = false.
Proof. vm_compute; reflexivity. Qed.
Example altered_root_rejected :
  F.check F.roots [F.q; F.neg F.p] F.claims F.single 6 = false.
Proof. vm_compute; reflexivity. Qed.
Example missing_root_rejected :
  F.check F.roots F.root_terms [(0,[4])] F.single 6 = false.
Proof. vm_compute; reflexivity. Qed.
Example dead_endpoint_rejected :
  F.check_single (EunoiaScope.Push 2 4 F.body
    (Some (F.close 11 4 F.scope_p [8] (F.scope_false 4 8))) F.finish) 6 = false.
Proof. vm_compute; reflexivity. Qed.
Example changed_certificate_rejected :
  F.check_single (EunoiaScope.Push 2 4 F.body
    (Some (F.close 3 4 F.scope_p [8] (F.copy 8))) F.finish) 6 = false.
Proof. vm_compute; reflexivity. Qed.
Example unused_step_after_conflict_rejected :
  F.check_single (EunoiaScope.Push 2 4 F.body (Some F.closing)
    (EunoiaScope.Next (F.step 5 [4] F.process_p [5] F.process_false)
      (EunoiaScope.Next (F.step 6 [0;5] F.contra_p [] (F.contradiction 4))
        (EunoiaScope.Next F.unsupported F.done)))) 6 = false.
Proof. vm_compute; reflexivity. Qed.
Example wrong_final_clause_rejected : F.check_single F.single 5 = false.
Proof. vm_compute; reflexivity. Qed.

(* Standalone entry points must keep rejecting invalid immutable tables. *)
Example standalone_eval_rejects_bad_names :
  @EunoiaScopedAdapter.eval F.sorts F.funcs F.atoms F.forms duplicate_names
    100 F.process_p [[8]] = None.
Proof. vm_compute; reflexivity. Qed.
Example standalone_scope_rejects_bad_names :
  @EunoiaScopedAdapter.scope_eval F.sorts F.funcs F.atoms F.forms duplicate_names
    100 F.scope_p 4 [] = None.
Proof. vm_compute; reflexivity. Qed.
Example standalone_gate_rejects_bad_atoms :
  @EunoiaLocal.gate F.sorts F.funcs (F.atoms.[1 <- Atom.Aapp 0 [1]]) F.forms
    [[4];[5]] [] (F.contradiction 4) = false.
Proof. vm_compute; reflexivity. Qed.
Print Assumptions scoped_positive.
Print Assumptions nested_positive.
Print Assumptions malformed_names_rejected.
Print Assumptions illtyped_tables_rejected.
Print Assumptions altered_root_rejected.
Print Assumptions missing_root_rejected.
Print Assumptions dead_endpoint_rejected.
Print Assumptions changed_certificate_rejected.
Print Assumptions unused_step_after_conflict_rejected.
Print Assumptions wrong_final_clause_rejected.
Print Assumptions standalone_eval_rejects_bad_names.
Print Assumptions standalone_scope_rejects_bad_names.
Print Assumptions standalone_gate_rejects_bad_atoms.
End EunoiaContextTests.
