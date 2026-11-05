(* SMTCoq -- distributed under the CeCILL-C licence (see LICENSE). *)
From Stdlib Require Import List String Bool Uint63.
From SMTCoq.checker.fol Require Import State Terms.
From SMTCoq.checker.eunoia Require Import EunoiaAdapter EunoiaChecker EunoiaScope
 EunoiaMemo EunoiaMemoTests.
From SMTCoq.checker.eunoia Require Import EunoiaSpecialized CpcSpecialized.
Import ListNotations.
Local Open Scope uint63_scope.
Local Open Scope string_scope.
Module T:=EunoiaMemoTests.
Definition implementations := [CpcSpecialized.r_636f6e747261; CpcSpecialized.r_70726f636573735f73636f7065].
Definition check_using implementations entries roots t:=@EunoiaSpecialized.checker T.S.sorts T.S.funcs T.S.atoms
 T.S.forms T.S.names implementations 100 entries 12 roots T.S.root_terms T.S.claims t 6.
Definition check := check_using implementations.
Example specialized_empty_registry :check_using [] T.entries T.S.roots T.shared=true.
Proof. vm_compute;reflexivity. Qed.
Example specialized_unrelated_registry :check_using [CpcSpecialized.r_7265666c] T.entries T.S.roots T.shared=true.
Proof. vm_compute;reflexivity. Qed.
Example specialized_scoped :check T.entries T.S.roots T.shared=true.
Proof. Time vm_compute;reflexivity. Qed.
Example specialized_bad_unused_certificate :check(T.entries++[T.invalid])T.S.roots T.shared=false.
Proof. vm_compute;reflexivity. Qed.
Example specialized_unsupported_source :
 check T.entries T.S.roots(EunoiaScope.Push 2 4
 (EunoiaScope.Next(T.step 3 [2;1]
 (EunoiaAdapter.Payload "unsupported"[][T.S.p;T.S.neg T.S.p]T.S.f[])[](T.M.Cached 0))T.done)
 (Some T.closing)T.finish)=false.
Proof. vm_compute;reflexivity. Qed.
Example specialized_wrong_roots :check T.entries(rev T.S.roots)T.shared=false.
Proof. vm_compute;reflexivity. Qed.
Example specialized_refutation_sound :~Forall(C.valid T.S.rho)T.S.roots.
Proof. eapply EunoiaSpecialized.checker_correct;exact specialized_scoped. Qed.
Print Assumptions specialized_refutation_sound.
