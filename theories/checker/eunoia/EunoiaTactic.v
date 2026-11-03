(**************************************************************************)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2026                                          *)
(*     Distributed under the terms of the CeCILL-C licence (see LICENSE). *)
(**************************************************************************)

From Stdlib Require Import List Bool Uint63.
From SMTCoq.utils Require Import PArray CompDec.
From SMTCoq.checker.fol Require Import State Terms.
From SMTCoq.checker.eunoia Require Import
  EoSyntax EunoiaChecker EunoiaAdapter EunoiaLocal.

Import ListNotations.
Local Open Scope uint63_scope.
Local Open Scope array_scope.

Module EunoiaTactic.

(* The proof file never chooses the theorem's authoritative assumptions. *)
Definition goal_roots (l : _lit) (b : bool) : list C.t :=
  [[if b then Lit.neg l else l]].

Lemma goal_roots_refute : forall rho l b,
  ~ Forall (C.valid rho) (goal_roots l b) -> Lit.interp rho l = b.
Proof.
  intros rho l b H; destruct b; destruct (Lit.interp rho l) eqn:Hl;
    try reflexivity; exfalso; apply H; unfold goal_roots;
    constructor; [ | constructor | | constructor]; unfold C.valid, C.interp;
    simpl; rewrite ?Lit.interp_neg, Hl; reflexivity.
Qed.

Section Tables.
  Variable t_i : array CompDec.typ_compdec.
  Variable t_func : array (Atom.tval t_i).
  Variable t_atom : array Atom.atom.
  Variable t_form : array Form.form.
  Variable names : EunoiaAdapter.naming.

  Definition valuation := @EunoiaLocal.valuation t_i t_func t_atom t_form.
  Definition trace := list
    (@EunoiaChecker.step EunoiaAdapter.rule_payload EunoiaLocal.witness).

  (* A concrete checked gate: no unproved gate hypothesis reaches the tactic. *)
  Definition checker fuel capacity roots root_terms claims (steps : trace) goal :=
    EunoiaAdapter.checker t_i t_func t_atom t_form names
      (@EunoiaLocal.gate t_i t_func t_atom t_form)
      fuel capacity roots root_terms claims steps goal.

  Lemma checker_tables : forall fuel capacity roots root_terms claims steps goal,
    checker fuel capacity roots root_terms claims steps goal = true ->
    EunoiaAdapter.tables_wf t_i t_func t_atom t_form names = true.
  Proof.
    intros fuel capacity roots root_terms claims steps goal H.
    unfold checker, EunoiaAdapter.checker in H.
    rewrite !andb_true_iff in H; tauto.
  Qed.

  Theorem checker_correct : forall fuel capacity roots root_terms claims steps goal,
    checker fuel capacity roots root_terms claims steps goal = true ->
    ~ Forall (C.valid valuation) roots.
  Proof.
    intros fuel capacity roots root_terms claims steps goal H.
    pose proof (checker_tables _ _ _ _ _ _ _ H) as Htables.
    unfold EunoiaAdapter.tables_wf in Htables.
    rewrite !andb_true_iff in Htables.
    destruct Htables as [[[Hnames Hform] Hatom] Hwt].
    eapply EunoiaAdapter.checker_correct; [ | | exact H].
    - unfold valuation, EunoiaLocal.valuation.
      apply (proj2 (Form.check_form_correct _ _ _ Hform)).
    - exact (@EunoiaLocal.gate_correct t_i t_func t_atom t_form Hwt).
  Qed.

  Definition checker_b fuel capacity l b root_terms claims steps goal :=
    checker fuel capacity (goal_roots l b) root_terms claims steps goal.

  Theorem checker_b_correct : forall fuel capacity l b root_terms claims steps goal,
    checker_b fuel capacity l b root_terms claims steps goal = true ->
    Lit.interp valuation l = b.
  Proof.
    intros fuel capacity l b root_terms claims steps goal H.
    apply goal_roots_refute; eapply checker_correct; exact H.
  Qed.

  (* Same signed Fiff convention as the existing SMTCoq Boolean-equality path. *)
  Definition checker_eq fuel capacity l1 l2 l root_terms claims steps goal :=
    if Lit.is_pos l then false else
      match t_form.[Lit.blit l] with
      | Form.Fiff a b => (l1 =? a) && (l2 =? b) &&
        checker_b fuel capacity (Lit.neg l) true root_terms claims steps goal
      | _ => false
      end.

  Theorem checker_eq_correct : forall fuel capacity l1 l2 l root_terms claims steps goal,
    checker_eq fuel capacity l1 l2 l root_terms claims steps goal = true ->
    Lit.interp valuation l1 = Lit.interp valuation l2.
  Proof.
    intros fuel capacity l1 l2 l root_terms claims steps goal H.
    unfold checker_eq in H.
    destruct (Lit.is_pos l) eqn:Hsign; try discriminate.
    destruct (t_form.[Lit.blit l]) as
      [a| | |n a|ls|ls|ls|a b|a b|a b c|a ls] eqn:Hiff;
      try discriminate.
    rewrite !andb_true_iff in H; destruct H as [[Ha Hb] Hrun].
    apply Uint63.eqb_spec in Ha; apply Uint63.eqb_spec in Hb.
    subst a b.
    pose proof (checker_b_correct _ _ _ _ _ _ _ _ Hrun) as Htruth.
    pose proof (checker_tables _ _ _ _ _ _ _ Hrun) as Htables.
    unfold EunoiaAdapter.tables_wf in Htables.
    rewrite !andb_true_iff in Htables.
    destruct Htables as [[[Hnames Hform] Hatom] Hwt].
    destruct (Form.check_form_correct
      (Atom.interp_form_hatom t_i t_func t_atom)
      (Atom.interp_form_hatom_bv t_i t_func t_atom) _ Hform)
      as [[Hdefault Hwf] _].
    unfold Lit.interp in Htruth.
    rewrite Lit.is_pos_neg, Hsign, Lit.blit_neg in Htruth; simpl in Htruth.
    unfold Var.interp, valuation, EunoiaLocal.valuation in Htruth.
    rewrite Form.wf_interp_form in Htruth by assumption.
    rewrite Hiff in Htruth.
    change (Bool.eqb (Lit.interp valuation l1) (Lit.interp valuation l2) = true)
      in Htruth.
    destruct (Lit.interp valuation l1), (Lit.interp valuation l2);
      simpl in Htruth; congruence.
  Qed.
End Tables.

End EunoiaTactic.
