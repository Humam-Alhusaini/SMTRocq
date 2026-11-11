(* SMTCoq -- distributed under the CeCILL-C licence (see LICENSE). *)
From Stdlib Require Import List Bool Uint63.
From SMTCoq.utils Require Import PArray.
From SMTCoq.checker.fol Require Import State Terms.
From SMTCoq.checker.eunoia Require Import EunoiaCertificate EunoiaMemoTests EunoiaTheory EunoiaChecker EunoiaScope EunoiaMemo EunoiaLocal.
Import ListNotations.
Local Open Scope uint63_scope.
Local Open Scope array_scope.
Module EunoiaCertificateTests.
Module K:=EunoiaCertificate.
Module T:=EunoiaMemoTests.
Module S:=T.S.
Module M:=EunoiaMemo.
Definition step:=@EunoiaChecker.Step C.t M.witness_ref.
Definition close:=@EunoiaScope.Discharge C.t M.witness_ref.
Definition done:K.trace:=EunoiaScope.Done.
Fixpoint compile (t:M.trace):K.trace:=
 match t with
 |EunoiaScope.Done=>done
 |EunoiaScope.Next st rest=>EunoiaScope.Next
   (step (EunoiaChecker.destination st)(EunoiaChecker.premises st)
    (EunoiaChecker.conclusion st)(EunoiaChecker.conclusion st)(EunoiaChecker.evidence st)) (compile rest)
 |EunoiaScope.Push slot a body closing rest=>EunoiaScope.Push slot a (compile body)
   (option_map(fun d=>close (EunoiaScope.endpoint d)(EunoiaScope.export_slot d)
    (EunoiaScope.scope_conclusion d)(EunoiaScope.scope_conclusion d)(EunoiaScope.scope_evidence d))closing)
   (compile rest)
 end.
Fixpoint append(t rest:K.trace):K.trace:=
 match t with
 |EunoiaScope.Done=>rest
 |EunoiaScope.Next st tail=>EunoiaScope.Next st(append tail rest)
 |EunoiaScope.Push slot a body closing tail=>EunoiaScope.Push slot a body closing(append tail rest)
 end.
Definition check cache roots claims t goal:=@K.checker S.sorts S.funcs S.atoms S.forms cache 12 roots claims t goal.
Definition shared:=compile T.shared.
Example scoped_refutation:check T.entries S.roots S.claims shared 6=true.
Proof. vm_compute;reflexivity. Qed.
Example scoped_refutation_sound:~Forall(C.valid S.rho)S.roots.
Proof. exact(@K.checker_correct S.sorts S.funcs S.atoms S.forms T.entries 12 S.roots S.claims shared 6 scoped_refutation). Qed.
Example wrong_roots:check T.entries [[4]] S.claims shared 6=false.
Proof. vm_compute;reflexivity. Qed.
Example injected_root_claim:check T.entries S.roots [(0,[]);(1,[5])] shared 6=false.
Proof. vm_compute;reflexivity. Qed.
Example wrong_final_clause:check T.entries S.roots S.claims shared 0=false.
Proof. vm_compute;reflexivity. Qed.
Example invalid_unused_entry:check(T.entries++[T.invalid])S.roots S.claims shared 6=false.
Proof. vm_compute;reflexivity. Qed.
Definition extra c w:=EunoiaScope.Next(step 7 [0] c c w)done.
Example checked_primitive_after_conflict:
 check T.entries S.roots S.claims(append shared(extra[4](M.Theory EunoiaTheory.Identity)))6=true.
Proof. vm_compute;reflexivity. Qed.
Example invalid_primitive_after_conflict:
 check T.entries S.roots S.claims(append shared(extra[4](M.Theory EunoiaTheory.Truth)))6=false.
Proof. vm_compute;reflexivity. Qed.
Example invalid_inline_after_conflict:
 check T.entries S.roots S.claims(append shared(extra[4](M.Inline T.invalid_witness)))6=false.
Proof. vm_compute;reflexivity. Qed.
Example dead_scope_read:
 check T.entries S.roots S.claims(append shared(EunoiaScope.Next
 (step 7 [2][4][4](M.Theory EunoiaTheory.Identity))done))6=false.
Proof. vm_compute;reflexivity. Qed.
Example reused_destination:
 check T.entries S.roots S.claims(append shared(EunoiaScope.Next
 (step 6 [0][4][4](M.Theory EunoiaTheory.Identity))done))6=false.
Proof. vm_compute;reflexivity. Qed.
Example out_of_bounds_clause:
 check T.entries S.roots S.claims(append shared(extra[100](M.Theory EunoiaTheory.Identity)))6=false.
Proof. vm_compute;reflexivity. Qed.
Example noncanonical_clause:
 check T.entries S.roots S.claims(append shared(extra[5;4](M.Theory EunoiaTheory.Identity)))6=false.
Proof. vm_compute;reflexivity. Qed.
Example missing_certificate:check[]S.roots S.claims shared 6=false.
Proof. vm_compute;reflexivity. Qed.
Definition invalid_theory:=M.TheoryEntry [[4]][5]EunoiaTheory.Identity.
Example invalid_unused_theory:check(T.entries++[invalid_theory])S.roots S.claims shared 6=false.
Proof. vm_compute;reflexivity. Qed.
Definition bad_atoms:=S.atoms.[1<-Atom.Aapp 0 [0]].
Example invalid_model:
 @K.checker S.sorts S.funcs bad_atoms S.forms T.entries 12 S.roots S.claims shared 6=false.
Proof. vm_compute;reflexivity. Qed.
Definition leaking_body:=EunoiaScope.Next(step 2 [0;1][][](M.Inline(S.contradiction 4)))done.
Definition leaking_trace:K.trace:=EunoiaScope.Push 1 5 leaking_body
 (Some(close 2 3 [4][4](M.Theory EunoiaTheory.Identity)))
 (EunoiaScope.Next(step 4 [2][][](M.Theory EunoiaTheory.Identity))done).
Example satisfiable_roots_cannot_import_local_conflict:
 check[][[4]][(0,[4])]leaking_trace 4=false.
Proof. vm_compute;reflexivity. Qed.
Print Assumptions scoped_refutation_sound.
End EunoiaCertificateTests.
