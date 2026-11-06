(* SMTCoq -- distributed under the CeCILL-C licence (see LICENSE). *)
From Stdlib Require Import List String Bool Uint63.
From SMTCoq.checker.fol Require Import State Terms.
From SMTCoq.checker.eunoia Require Import EunoiaAdapter EunoiaChecker EunoiaScope
 EunoiaMemo EunoiaMemoTests.
From SMTCoq.checker.eunoia Require Import EunoiaStaged.
Import ListNotations.
Local Open Scope uint63_scope.
Local Open Scope string_scope.
Module T:=EunoiaMemoTests.
Definition check entries roots t:=@EunoiaStaged.checker T.S.sorts T.S.funcs T.S.atoms
 T.S.forms T.S.names 100 entries 12 roots T.S.root_terms T.S.claims t 6.
Example staged_scoped :check T.entries T.S.roots T.shared=true.
Proof. Time vm_compute;reflexivity. Qed.
Example staged_bad_unused_certificate :check(T.entries++[T.invalid])T.S.roots T.shared=false.
Proof. vm_compute;reflexivity. Qed.
Example staged_unsupported_source :
 check T.entries T.S.roots(EunoiaScope.Push 2 4
 (EunoiaScope.Next(T.step 3 [2;1]
 (EunoiaAdapter.Payload "unsupported"[][T.S.p;T.S.neg T.S.p]T.S.f[])[](T.M.Cached 0))T.done)
 (Some T.closing)T.finish)=false.
Proof. vm_compute;reflexivity. Qed.
Example staged_wrong_roots :check T.entries(rev T.S.roots)T.shared=false.
Proof. vm_compute;reflexivity. Qed.
Example staged_refutation_sound :~Forall(C.valid T.S.rho)T.S.roots.
Proof. eapply EunoiaStaged.checker_correct;exact staged_scoped. Qed.
Print Assumptions staged_refutation_sound.
