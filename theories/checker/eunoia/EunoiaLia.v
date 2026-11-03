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

From Stdlib Require Import Bool List Uint63 ZMicromega.
From SMTCoq.utils Require Import Misc PArray.
From SMTCoq.checker.fol Require Import State Terms.
From SMTCoq.checker.small_checker.lia Require Import LIA.

Import ListNotations.

(* A semantic certificate gate, independent of CPC rule names. The generated
   CPC evaluator must separately check the rule, its side conditions, and the
   binding of these literals to the exact step premises and conclusion.
   In particular this gate does not check an entire CPC proof. *)
Module EunoiaLia.

  Section Certificate.
    Variables (t_form : array Form.form) (t_atom : array Atom.atom).

    (* Unlike [check_micromega], failure is explicit, even for [C._true]. *)
    Definition check_clause (cl : C.t) (cert : list ZArithProof) : bool :=
      match LIA.build_clause t_form t_atom LIA.empty_vmap cl with
      | Some (_, bf) => ZTautoChecker bf cert
      | None => false
      end.

    Lemma check_clause_result cl cert :
      check_clause cl cert = true ->
      LIA.check_micromega t_form t_atom cl cert = cl.
    Proof.
      unfold check_clause, LIA.check_micromega.
      destruct (LIA.build_clause t_form t_atom LIA.empty_vmap cl)
        as [[vm bf] | ]; [ | discriminate].
      intro H; now rewrite H.
    Qed.

    Lemma check_clause_unsupported cl cert :
      LIA.build_clause t_form t_atom LIA.empty_vmap cl = None ->
      check_clause cl cert = false.
    Proof. unfold check_clause; intro H; now rewrite H. Qed.

    (* Keep each premise as a formula literal, including disjunctions; do not
       flatten premise clauses into a conjunction of their disjuncts. *)
    Definition step_clause (premises : list _lit) (conclusion : _lit) : C.t :=
      map Lit.neg premises ++ [conclusion].

    Definition check_step premises conclusion cert : bool :=
      check_clause (step_clause premises conclusion) cert.

    Section Soundness.
      Variables (t_i : array CompDec.typ_compdec)
                (t_func : array (Atom.tval t_i))
                (ch_atom : Atom.check_atom t_atom)
                (ch_form : Form.check_form t_form)
                (wt_t_atom : Atom.wt t_i t_func t_atom).

      Let rho := Form.interp_state_var
        (Atom.interp_form_hatom t_i t_func t_atom)
        (Atom.interp_form_hatom_bv t_i t_func t_atom) t_form.

      Lemma check_clause_sound cl cert :
        check_clause cl cert = true -> C.valid rho cl.
      Proof.
        intro H; rewrite <- (check_clause_result cl cert H).
        exact (LIA.valid_check_micromega t_form t_atom t_i t_func
          ch_atom ch_form wt_t_atom cl cert).
      Qed.

      Lemma check_step_sound premises conclusion cert :
        check_step premises conclusion cert = true ->
        forallb (Lit.interp rho) premises = true ->
        Lit.interp rho conclusion = true.
      Proof.
        intros Hcheck Hpremises.
        pose proof (check_clause_sound _ cert Hcheck) as Hvalid.
        unfold C.valid, C.interp, step_clause in Hvalid.
        rewrite existsb_app in Hvalid.
        change (C.interp rho (map Lit.neg premises) ||
          (Lit.interp rho conclusion || false) = true) in Hvalid.
        rewrite C.Cinterp_neg, Hpremises in Hvalid.
        simpl in Hvalid; now rewrite orb_false_r in Hvalid.
      Qed.
    End Soundness.
  End Certificate.
End EunoiaLia.

Print Assumptions EunoiaLia.check_clause_result.
Print Assumptions EunoiaLia.check_clause_unsupported.
Print Assumptions EunoiaLia.check_clause_sound.
Print Assumptions EunoiaLia.check_step_sound.
