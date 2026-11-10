(* SMTCoq -- distributed under the CeCILL-C licence (see LICENSE). *)
From Stdlib Require Import List Bool String Uint63 ZArith ZMicromega RingMicromega EnvRing.
From SMTCoq.utils Require Import PArray CompDec.
From SMTCoq.structures Require Import CompDecInstances.
From SMTCoq.checker.fol Require Import State Terms.
From SMTCoq.checker.eunoia Require Import EunoiaLocal EunoiaTheory EunoiaMemo
 EunoiaMemoTests EunoiaScope EunoiaAdapter EunoiaLiaTests.
Import ListNotations.
Local Open Scope uint63_scope.
Local Open Scope array_scope.
Local Open Scope string_scope.
Module EunoiaTheoryTests.
Module P := EunoiaTheory.
Definition sorts : array typ_compdec := make 1 unit_typ_compdec.
Definition funcs : array (Atom.tval sorts) :=
 (make 5 (@Atom.Tval sorts ([],Typ.TZ) 0%Z))
 .[3 <- @Atom.Tval sorts ([Typ.TZ],Typ.TZ) (fun x:Z => (x+1)%Z)]
 .[4 <- @Atom.Tval sorts ([Typ.TZ],Typ.TZ) (fun x:Z => (x+2)%Z)].
Definition atoms : array Atom.atom :=
 (make 14 (Atom.Acop Atom.CO_xH))
 .[1 <- Atom.Aapp 0 []].[2 <- Atom.Aapp 1 []].[3 <- Atom.Aapp 2 []]
 .[4 <- Atom.Abop (Atom.BO_eq Typ.TZ) 1 2]
 .[5 <- Atom.Abop (Atom.BO_eq Typ.TZ) 2 3]
 .[6 <- Atom.Abop (Atom.BO_eq Typ.TZ) 1 3]
 .[7 <- Atom.Abop (Atom.BO_eq Typ.TZ) 1 1]
 .[8 <- Atom.Aapp 3 [1]].[9 <- Atom.Aapp 3 [2]]
 .[10 <- Atom.Abop (Atom.BO_eq Typ.TZ) 8 9]
 .[11 <- Atom.Aapp 4 [2]].[12 <- Atom.Abop (Atom.BO_eq Typ.TZ) 8 11]
 .[13 <- Atom.Abop (Atom.BO_eq Typ.TZ) 2 1].
Definition forms : array Form.form :=
 (make 9 Form.Ftrue).[1 <- Form.Ffalse]
 .[2 <- Form.Fatom 4].[3 <- Form.Fatom 5].[4 <- Form.Fatom 6]
 .[5 <- Form.Fatom 7].[6 <- Form.Fatom 10].[7 <- Form.Fatom 12].[8 <- Form.Fatom 13].
Definition gate := @P.gate sorts funcs atoms forms.
Example checked_tables : Form.check_form forms = true /\ Atom.check_atom atoms = true /\
 Atom.wt sorts funcs atoms = true.
Proof. vm_compute; repeat split; reflexivity. Qed.
Example reflexivity : gate [] [10] P.Trans = true.
Proof. vm_compute; reflexivity. Qed.
Example transitivity : gate [[4];[6]] [8] P.Trans = true.
Proof. vm_compute; reflexivity. Qed.
Example symmetry : gate [[4]] [16] P.Trans = true.
Proof. vm_compute; reflexivity. Qed.
Example wrong_endpoint : gate [[4];[6]] [4] P.Trans = false.
Proof. vm_compute; reflexivity. Qed.
Example missing_link : gate [[4]] [8] P.Trans = false.
Proof. vm_compute; reflexivity. Qed.
Example negative_premise_rejected : gate [[5];[6]] [8] P.Trans = false.
Proof. vm_compute; reflexivity. Qed.
Example nonunit_premise_uses_fallback : gate [[4;6]] [8] P.Trans = false.
Proof. vm_compute; reflexivity. Qed.
Example trans_true_fallback_rejected : gate [] [0] P.Trans = false.
Proof. vm_compute; reflexivity. Qed.
Example explicit_truth : gate [] [0] P.Truth = true.
Proof. vm_compute; reflexivity. Qed.
Example truth_wrong_conclusion : gate [] [4] P.Truth = false.
Proof. vm_compute; reflexivity. Qed.
Example identity : gate [[4];[6]] [4] P.Identity = true.
Proof. vm_compute; reflexivity. Qed.
Example identity_missing : gate [] [4] P.Identity = false.
Proof. vm_compute; reflexivity. Qed.
Example invalid_unused_premise_rejected : gate [[4];[100]] [4] P.Identity = false.
Proof. vm_compute; reflexivity. Qed.
Example out_of_bounds_conclusion : gate [[4]] [100] P.Identity = false.
Proof. vm_compute; reflexivity. Qed.
Example unchecked_table_rejected : P.prepared_gate forms atoms false [[4];[6]] [8] P.Trans = false.
Proof. vm_compute; reflexivity. Qed.
Example congruence : gate [[4]] [12] (P.Congruence [Some 4]) = true.
Proof. vm_compute; reflexivity. Qed.
Example congruence_missing_equality : gate [[4]] [12] (P.Congruence [None]) = false.
Proof. vm_compute; reflexivity. Qed.
Example congruence_wrong_arity : gate [[4]] [12] (P.Congruence [Some 4;None]) = false.
Proof. vm_compute; reflexivity. Qed.
Example congruence_wrong_function : gate [[4]] [14] (P.Congruence [Some 4]) = false.
Proof. vm_compute; reflexivity. Qed.
Example checked_transitivity_is_sound :
 Forall (C.valid (@EunoiaLocal.valuation sorts funcs atoms forms)) [[4];[6]] ->
 C.valid (@EunoiaLocal.valuation sorts funcs atoms forms) [8].
Proof.
 exact (@P.gate_correct sorts funcs atoms forms
   (proj2 (proj2 checked_tables)) [[4];[6]] [8] P.Trans transitivity).
Qed.

(* Arithmetic computation controls reuse the original checker fixtures. These
   examples assert Boolean behavior; generic soundness is proved in P.gate_correct. *)
Module A := EunoiaLiaTests.
Definition arithmetic := P.prepared_gate A.forms A.atoms true.
Example linear_reflexivity : arithmetic [] [14] (P.Linear []) = true.
Proof. vm_compute; reflexivity. Qed.
Example linear_rejects_false : arithmetic [] [] (P.Linear []) = false.
Proof. vm_compute; reflexivity. Qed.
Definition scaled_proof : list ZArithProof :=
 A.scale_cert.
Example linear_scaling : arithmetic [[4]] [10] (P.Linear scaled_proof) = true.
Proof. vm_compute; reflexivity. Qed.
Example linear_missing_proof : arithmetic [[4]] [10] (P.Linear []) = false.
Proof. vm_compute; reflexivity. Qed.
Example linear_changed_coefficient : arithmetic [[4]] [10]
 (P.Linear [RatProof (PsatzAdd (PsatzIn _ 0)
   (PsatzMulE (PsatzC 3%Z) (PsatzIn _ 1))) DoneProof]) = false.
Proof. vm_compute; reflexivity. Qed.
Example linear_missing_premise : arithmetic [] [10] (P.Linear scaled_proof) = false.
Proof. vm_compute; reflexivity. Qed.
Example linear_changed_premise : arithmetic [[6]] [10] (P.Linear scaled_proof) = false.
Proof. vm_compute; reflexivity. Qed.

Module T := EunoiaMemoTests.
Module S := T.S.
Fixpoint append (t rest:EunoiaMemo.trace) : EunoiaMemo.trace :=
 match t with
 | EunoiaScope.Done => rest
 | EunoiaScope.Next st tail => EunoiaScope.Next st (append tail rest)
 | EunoiaScope.Push slot a body closing tail => EunoiaScope.Push slot a body closing (append tail rest)
 end.
Definition resolve_identity := EunoiaAdapter.Payload "resolution" [EoSyntax.Symbol "true";S.q]
 [S.p;S.f] S.p [4].
Definition extra payload premise c := EunoiaScope.Next
 (T.step 7 [premise;6] payload c (EunoiaMemo.Theory P.Identity)) T.done.
Example complete_source_and_semantics : T.check T.entries (append T.shared (extra resolve_identity 0 [4])) = true.
Proof. vm_compute; reflexivity. Qed.
Definition unsupported := EunoiaAdapter.Payload "unsupported" [S.p] [S.p] S.p [4].
Example unsupported_after_conflict_rejected :
 T.check T.entries (append T.shared (extra unsupported 0 [4])) = false.
Proof. vm_compute; reflexivity. Qed.
Example wrong_source_binding_rejected :
 T.check T.entries (append T.shared (extra resolve_identity 1 [5])) = false.
Proof. vm_compute; reflexivity. Qed.
Example invalid_primitive_after_conflict_rejected :
 T.check T.entries (append T.shared (EunoiaScope.Next
  (T.step 7 [0;6] resolve_identity [4] (EunoiaMemo.Theory P.Truth)) T.done)) = false.
Proof. vm_compute; reflexivity. Qed.
Definition shared_identity := EunoiaMemo.TheoryEntry [[4];[]] [4] P.Identity.
Definition invalid_identity := EunoiaMemo.TheoryEntry [[4];[]] [5] P.Identity.
Definition cached_extra := EunoiaScope.Next
 (T.step 7 [0;6] resolve_identity [4] (EunoiaMemo.Cached 3)) T.done.
Example checked_shared_primitive :
 T.check (T.entries ++ [shared_identity]) (append T.shared cached_extra) = true.
Proof. vm_compute; reflexivity. Qed.
Example unused_invalid_primitive_entry_rejected :
 T.check (T.entries ++ [invalid_identity]) T.shared = false.
Proof. vm_compute; reflexivity. Qed.
Example invalid_referenced_primitive_entry_rejected :
 T.check (T.entries ++ [invalid_identity]) (append T.shared cached_extra) = false.
Proof. vm_compute; reflexivity. Qed.
Example ordered_shared_primitive_premises :
 T.gate [EunoiaMemo.TheoryEntry [[4];[5]] [4] P.Identity]
 [[5];[4]] [4] (EunoiaMemo.Cached 0) = false.
Proof. vm_compute; reflexivity. Qed.
Example full_refutation_sound : ~ Forall (C.valid S.rho) S.roots.
Proof. eapply EunoiaMemo.checker_correct; exact complete_source_and_semantics. Qed.
Print Assumptions full_refutation_sound.
End EunoiaTheoryTests.
