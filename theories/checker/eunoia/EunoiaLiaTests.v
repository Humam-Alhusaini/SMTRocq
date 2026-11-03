(**************************************************************************)
(*     SMTCoq -- distributed under the terms of the CeCILL-C licence       *)
(**************************************************************************)

From Stdlib Require Import Bool List Uint63 ZArith ZMicromega RingMicromega EnvRing.
From SMTCoq.utils Require Import PArray.
From SMTCoq.checker.fol Require Import State Terms.
From SMTCoq.checker.small_checker.lia Require Import LIA.
From SMTCoq.checker.eunoia Require Import EunoiaLia.

Import ListNotations.
Local Open Scope uint63_scope.
Local Open Scope array_scope.

Module EunoiaLiaTests.
  Import Atom EunoiaLia.

  (* x is the single opaque integer term; arithmetic operations are the
     existing SMTCoq ones. No CPC/SMT-LIB interpretation is defined here. *)
  Definition atoms : array atom :=
    (make 14 (Acop CO_xH)).[1 <- Acop CO_Z0]
      .[2 <- Auop UO_Zpos 0]
      .[3 <- Aapp 0 []]
      .[4 <- Abop BO_Zle 3 1]          (* x <= 0 *)
      .[5 <- Abop BO_Zle 3 2]          (* x <= 1 *)
      .[6 <- Abop BO_Zlt 3 1]          (* x < 0 *)
      .[7 <- Auop UO_xO 0]
      .[8 <- Auop UO_Zpos 7]
      .[9 <- Abop BO_Zmult 8 3]        (* 2*x *)
      .[10 <- Abop BO_Zle 9 1]        (* 2*x <= 0 *)
      .[11 <- Abop BO_Zlt 9 1]        (* 2*x < 0 *)
      .[12 <- Abop (BO_eq Typ.TZ) 3 3]
      .[13 <- Abop (BO_eq Typ.Tbool) 3 3].

  Definition forms : array Form.form :=
    (make 10 Form.Ftrue).[1 <- Form.Ffalse]
      .[2 <- Form.Fatom 4].[3 <- Form.Fatom 5]
      .[4 <- Form.Fatom 6].[5 <- Form.Fatom 10]
      .[6 <- Form.Fatom 11].[7 <- Form.Fatom 12]
      .[8 <- Form.Fatom 13].[9 <- Form.Fatom 3].

  (* Two inequalities, multiplied by 2 and 1 respectively. *)
  Definition scale_cert : list ZArithProof :=
    [RatProof (PsatzAdd (PsatzIn _ 0)
                       (PsatzMulE (PsatzC 2%Z) (PsatzIn _ 1))) DoneProof].

  Example reflexivity_accepted :
    check_step forms atoms [] (Lit.lit 7) [] = true.
  Proof. vm_compute. reflexivity. Qed.

  Example weakening_accepted :
    check_step forms atoms [Lit.lit 2] (Lit.lit 3) [] = true.
  Proof. vm_compute. reflexivity. Qed.

  Example scaling_accepted :
    check_step forms atoms [Lit.lit 2] (Lit.lit 5) scale_cert = true.
  Proof. vm_compute. reflexivity. Qed.

  Example strict_conclusion_rejected :
    check_step forms atoms [Lit.lit 2] (Lit.lit 6) scale_cert = false.
  Proof. vm_compute. reflexivity. Qed.

  Example missing_certificate_rejected :
    check_step forms atoms [Lit.lit 2] (Lit.lit 5) [] = false.
  Proof. vm_compute. reflexivity. Qed.

  Example changed_coefficient_rejected :
    check_step forms atoms [Lit.lit 2] (Lit.lit 5)
      [RatProof (PsatzAdd (PsatzIn _ 0)
         (PsatzMulE (PsatzC 3%Z) (PsatzIn _ 1))) DoneProof] = false.
  Proof. vm_compute. reflexivity. Qed.

  Example missing_premise_rejected :
    check_step forms atoms [] (Lit.lit 5) scale_cert = false.
  Proof. vm_compute. reflexivity. Qed.

  Example changed_premise_rejected :
    check_step forms atoms [Lit.lit 3] (Lit.lit 5) scale_cert = false.
  Proof. vm_compute. reflexivity. Qed.

  Example reversed_implication_rejected :
    check_step forms atoms [Lit.lit 3] (Lit.lit 2) [] = false.
  Proof. vm_compute. reflexivity. Qed.

  Example unsupported_boolean_atom_rejected :
    check_step forms atoms [] (Lit.lit 9) [] = false.
  Proof. vm_compute. reflexivity. Qed.

  Example unsupported_equality_type_rejected :
    check_step forms atoms [] (Lit.lit 8) [] = false.
  Proof. vm_compute. reflexivity. Qed.

  Example empty_clause_rejected :
    check_clause forms atoms [] [] = false.
  Proof. vm_compute. reflexivity. Qed.

  Example fallback_is_not_acceptance :
    LIA.check_micromega forms atoms [] [] = C._true /\
    check_clause forms atoms [] [] = false.
  Proof. vm_compute. split; reflexivity. Qed.
End EunoiaLiaTests.
