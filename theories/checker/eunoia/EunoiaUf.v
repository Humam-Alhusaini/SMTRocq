(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2026                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

From Stdlib Require Import Bool List Uint63.
From SMTCoq.utils Require Import Misc PArray CompDec.
From SMTCoq.checker.fol Require Import State Terms.
From SMTCoq.checker.small_checker.euf Require Import EUF.

Import ListNotations.
Local Open Scope uint63_scope.
Local Open Scope array_scope.

(* These are bridges to the existing EUF certificates, not CPC rule
   implementations.  The signature-generated evaluator must independently
   establish each CPC rule application.  Its exact signed premises and result
   must also match the clause checked here: EUF failure returns C._true, and
   EUF's equality accessors erase literal polarity. *)

Lemma unit_consequence rho premises conclusion :
  C.valid rho (conclusion :: List.map Lit.neg premises) ->
  List.forallb (Lit.interp rho) premises ->
  Lit.interp rho conclusion.
Proof.
  unfold C.valid; intros Hcl Hprem.
  change (Lit.interp rho conclusion ||
          C.interp rho (List.map Lit.neg premises) = true) in Hcl.
  rewrite C.Cinterp_neg, Hprem, orb_false_r in Hcl.
  exact Hcl.
Qed.

Section Certificates.
  Variables (t_form : PArray.array Form.form)
            (t_atom : PArray.array Atom.atom)
            (t_i : PArray.array CompDec.typ_compdec)
            (t_func : PArray.array (Atom.tval t_i)).
  Hypotheses (ch_atom : Atom.check_atom t_atom)
             (ch_form : Form.check_form t_form)
             (wt_t_atom : Atom.wt t_i t_func t_atom).

  Local Abbreviation rho :=
    (Form.interp_state_var (Atom.interp_form_hatom t_i t_func t_atom)
       (Atom.interp_form_hatom_bv t_i t_func t_atom) t_form).

  (* The equality is an obligation for the caller's reflected clause
     comparison.  No inference follows merely from a nonempty EUF result. *)
  Lemma trans_clause_sound res eqs clause :
    EUF.check_trans t_form t_atom res eqs = clause -> C.valid rho clause.
  Proof.
    intros <-.
    exact (EUF.valid_check_trans t_form t_atom t_i t_func
             ch_atom ch_form wt_t_atom res eqs).
  Qed.

  Lemma congr_clause_sound res eqs clause :
    EUF.check_congr t_form t_atom res eqs = clause -> C.valid rho clause.
  Proof.
    intros <-.
    exact (EUF.valid_check_congr t_form t_atom t_i t_func
             ch_atom ch_form wt_t_atom res eqs).
  Qed.

  Lemma pred_congr_clause_sound pa pb eqs clause :
    EUF.check_congr_pred t_form t_atom pa pb eqs = clause ->
    C.valid rho clause.
  Proof.
    intros <-.
    exact (EUF.valid_check_congr_pred t_form t_atom t_i t_func
             ch_atom ch_form wt_t_atom pa pb eqs).
  Qed.

  (* To prove ~forward -> ~backward, certify backward -> forward.
     Passing negative literals directly to check_trans does not achieve this:
     that checker strips their signs. *)
  Lemma neg_symm_step_sound forward backward :
    EUF.check_trans t_form t_atom forward [backward] =
      [forward; Lit.neg backward] ->
    Lit.interp rho (Lit.neg forward) ->
    Lit.interp rho (Lit.neg backward).
  Proof.
    intros Hcheck Hforward.
    pose proof (trans_clause_sound _ _ _ Hcheck) as Hcl.
    unfold C.valid in Hcl.
    change (Lit.interp rho forward ||
            (Lit.interp rho (Lit.neg backward) || false) = true) in Hcl.
    rewrite Lit.interp_neg in Hforward.
    apply negb_true_iff in Hforward.
    rewrite Hforward, orb_false_l, orb_false_r in Hcl.
    exact Hcl.
  Qed.
End Certificates.

(* Kernel-computed interface regressions.  These small tables exercise syntax
   checking only; they do not assert that unchecked tables are well typed.
   Production uses the checked-table hypotheses of the lemmas above. *)
Module Regression.
  Definition atoms : PArray.array Atom.atom :=
    (PArray.make 16 (Atom.Acop Atom.CO_xH))
      .[0 <- Atom.Aapp 0 []]          (* x *)
      .[1 <- Atom.Aapp 1 []]          (* y *)
      .[2 <- Atom.Aapp 2 []]          (* z *)
      .[3 <- Atom.Abop (Atom.BO_eq Typ.TZ) 0 1]
      .[4 <- Atom.Abop (Atom.BO_eq Typ.TZ) 1 2]
      .[5 <- Atom.Abop (Atom.BO_eq Typ.TZ) 0 2]
      .[6 <- Atom.Abop (Atom.BO_eq Typ.TZ) 1 0]
      .[7 <- Atom.Abop (Atom.BO_eq Typ.TZ) 0 0]
      .[8 <- Atom.Aapp 3 [2; 0]]     (* f z x *)
      .[9 <- Atom.Aapp 3 [2; 1]]     (* f z y *)
      .[10 <- Atom.Aapp 4 [2; 1]]    (* g z y *)
      .[11 <- Atom.Abop (Atom.BO_eq Typ.TZ) 8 9]
      .[12 <- Atom.Abop (Atom.BO_eq Typ.TZ) 8 10]
      .[13 <- Atom.Aapp 5 [2; 0]]    (* P z x *)
      .[14 <- Atom.Aapp 5 [2; 1]].   (* P z y *)

  Definition forms : PArray.array Form.form :=
    (PArray.make 13 Form.Ftrue)
      .[1 <- Form.Ffalse]
      .[2 <- Form.Fatom 3]          (* x = y, literal 4 *)
      .[3 <- Form.Fatom 4]          (* y = z, literal 6 *)
      .[4 <- Form.Fatom 5]          (* x = z, literal 8 *)
      .[5 <- Form.Fatom 6]          (* y = x, literal 10 *)
      .[6 <- Form.Fatom 7]          (* x = x, literal 12 *)
      .[7 <- Form.Fatom 11]         (* f z x = f z y, literal 14 *)
      .[8 <- Form.Fatom 12]         (* f z x = g z y, literal 16 *)
      .[9 <- Form.Fatom 13]         (* P z x, literal 18 *)
      .[10 <- Form.Fatom 14]        (* P z y, literal 20 *)
      .[11 <- Form.Fiff 4 10]       (* Boolean equality is a form *)
      .[12 <- Form.Fatom 0].        (* non-equality atom *)

  Example reflexivity_clause : EUF.check_trans forms atoms 12 [] = [12].
  Proof. vm_compute; reflexivity. Qed.

  Example symmetry_clause : EUF.check_trans forms atoms 10 [4] = [10; 5].
  Proof. vm_compute; reflexivity. Qed.

  Example transitivity_clause :
    EUF.check_trans forms atoms 8 [4; 6] = [8; 7; 5].
  Proof. vm_compute; reflexivity. Qed.

  Example reversed_equality_clause :
    EUF.check_trans forms atoms 8 [10; 6] = [8; 7; 11].
  Proof. vm_compute; reflexivity. Qed.

  Example congruence_clause :
    EUF.check_congr forms atoms 14 [None; Some 4] = [5; 14].
  Proof. vm_compute; reflexivity. Qed.

  Example predicate_congruence_clause :
    EUF.check_congr_pred forms atoms 18 20 [None; Some 4] = [5; 19; 20].
  Proof. vm_compute; reflexivity. Qed.

  Example reject_nonreflexive : EUF.check_trans forms atoms 4 [] = C._true.
  Proof. vm_compute; reflexivity. Qed.

  Example reject_disconnected_chain :
    EUF.check_trans forms atoms 8 [12; 6] = C._true.
  Proof. vm_compute; reflexivity. Qed.

  Example reject_wrong_endpoint :
    EUF.check_trans forms atoms 10 [4; 6] = C._true.
  Proof. vm_compute; reflexivity. Qed.

  Example reject_nonequality : EUF.check_trans forms atoms 24 [] = C._true.
  Proof. vm_compute; reflexivity. Qed.

  Example reject_formula_as_atom_equality :
    EUF.check_trans forms atoms 22 [] = C._true.
  Proof. vm_compute; reflexivity. Qed.

  Example reject_congruence_head :
    EUF.check_congr forms atoms 16 [None; Some 4] = C._true.
  Proof. vm_compute; reflexivity. Qed.

  Example reject_congruence_arity :
    EUF.check_congr forms atoms 14 [Some 4] = C._true.
  Proof. vm_compute; reflexivity. Qed.

  Example reject_missing_argument_equality :
    EUF.check_congr forms atoms 14 [None; None] = C._true.
  Proof. vm_compute; reflexivity. Qed.

  Example reject_wrong_argument_equality :
    EUF.check_congr forms atoms 14 [None; Some 6] = C._true.
  Proof. vm_compute; reflexivity. Qed.

  (* Evidence that sign checking belongs to the exact clause binding. *)
  Example equality_checker_erases_sign :
    EUF.check_trans forms atoms 10 [5] = [10; 5].
  Proof. vm_compute; reflexivity. Qed.

  Example reject_out_of_bounds_equality :
    EUF.check_trans forms atoms 198 [] = C._true.
  Proof. vm_compute; reflexivity. Qed.

  Example reject_predicate_argument_equality :
    EUF.check_congr_pred forms atoms 18 20 [None; Some 6] = C._true.
  Proof. vm_compute; reflexivity. Qed.

  Example reject_negative_premise_binding :
    EUF.check_trans forms atoms 10 [5] <> [10; Lit.neg 5].
  Proof. vm_compute; discriminate. Qed.

  Example reject_negative_conclusion_binding :
    EUF.check_trans forms atoms 11 [4] <> [11; Lit.neg 4].
  Proof. vm_compute; discriminate. Qed.

  Example failure_is_not_requested_clause :
    EUF.check_congr forms atoms 14 [None; None] <> [14; Lit.neg 4].
  Proof. vm_compute; discriminate. Qed.
End Regression.
