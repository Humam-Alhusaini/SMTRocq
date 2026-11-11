(* SMTCoq -- distributed under the CeCILL-C licence (see LICENSE).
   Semantic certificates compiled from untrusted solver proofs. This checker
   proves the SMT theorem; CPC source conformance remains a separate checker. *)
From Stdlib Require Import List Bool Uint63.
From SMTCoq.utils Require Import PArray CompDec.
From SMTCoq.checker.fol Require Import State Terms.
From SMTCoq.checker.eunoia Require Import EoSyntax EunoiaAdapter EunoiaLocal EunoiaScope EunoiaMemo EunoiaTactic.
Import ListNotations.
Local Open Scope uint63_scope.
Local Open Scope array_scope.
Set Implicit Arguments.
Module EunoiaCertificate.
Definition trace := @EunoiaScope.trace C.t C.t EunoiaMemo.witness_ref.
Definition discharge := @EunoiaScope.discharge C.t EunoiaMemo.witness_ref.
Definition clause_eval (c:C.t) (_:list C.t) := Some c.
Definition scope_eval (c:C.t) (_:_lit) (_:C.t) := Some c.
Section Tables.
Variable t_i:array typ_compdec.
Variable t_func:array(Atom.tval t_i).
Variable t_atom:array Atom.atom.
Variable t_form:array Form.form.
Definition valuation := @EunoiaLocal.valuation t_i t_func t_atom t_form.
Definition checker entries capacity roots claims (t:trace) goal :=
 Form.check_form t_form && Atom.check_atom t_atom && Atom.wt t_i t_func t_atom &&
 @EunoiaMemo.cache_valid t_i t_func t_atom t_form entries &&
 EunoiaScope.checker clause_eval scope_eval
 (@EunoiaMemo.gate t_i t_func t_atom t_form entries)
 (PArray.length t_form) capacity roots claims t goal.
Lemma checker_tables : forall entries capacity roots claims t goal,
 checker entries capacity roots claims t goal=true ->
 (Form.check_form t_form=true /\ Atom.check_atom t_atom=true) /\ Atom.wt t_i t_func t_atom=true.
Proof. intros;unfold checker in H;rewrite !andb_true_iff in H;tauto. Qed.
Theorem checker_correct : forall entries capacity roots claims t goal,
 checker entries capacity roots claims t goal=true ->
 ~Forall(C.valid valuation)roots.
Proof.
 intros entries capacity roots claims t goal H.
 unfold checker in H;rewrite !andb_true_iff in H.
 destruct H as [[[[Hform Hatom] Hwt] Hcache] H].
 eapply EunoiaScope.checker_correct;[| |exact H].
 - unfold valuation,EunoiaLocal.valuation;apply(proj2(Form.check_form_correct _ _ _ Hform)).
 - exact (@EunoiaMemo.gate_correct t_i t_func t_atom t_form entries Hwt Hcache).
Qed.
Definition checker_b entries capacity l b claims t goal :=
 checker entries capacity(EunoiaTactic.goal_roots l b)claims t goal.
Theorem checker_b_correct : forall entries capacity l b claims t goal,
 checker_b entries capacity l b claims t goal=true -> Lit.interp valuation l=b.
Proof.
 intros entries capacity l b claims t goal H.
 apply EunoiaTactic.goal_roots_refute.
 exact (@checker_correct entries capacity (EunoiaTactic.goal_roots l b) claims t goal H).
Qed.
Definition checker_eq entries capacity l1 l2 l claims t goal :=
 if Lit.is_pos l then false else match t_form.[Lit.blit l]with
 |Form.Fiff a b=>(l1 =? a)&&(l2 =? b)&&checker_b entries capacity(Lit.neg l)true claims t goal
 |_=>false end.
  Theorem checker_eq_correct : forall entries capacity l1 l2 l claims t goal,
    checker_eq entries capacity l1 l2 l claims t goal = true ->
    Lit.interp valuation l1 = Lit.interp valuation l2.
  Proof.
    intros entries capacity l1 l2 l claims t goal H.
    unfold checker_eq in H.
    destruct (Lit.is_pos l) eqn:Hsign; try discriminate.
    destruct (t_form.[Lit.blit l]) as
      [a| | |n a|ls|ls|ls|a b|a b|a b c|a ls] eqn:Hiff; try discriminate.
    rewrite !andb_true_iff in H; destruct H as [[Ha Hb] Hrun].
    apply Uint63.eqb_spec in Ha; apply Uint63.eqb_spec in Hb; subst a b.
    pose proof (@checker_b_correct entries capacity (Lit.neg l) true claims t goal Hrun) as Htruth.
    pose proof (@checker_tables entries capacity (EunoiaTactic.goal_roots (Lit.neg l) true) claims t goal Hrun) as [[Hform Hatom] Hwt].
    destruct (Form.check_form_correct
      (Atom.interp_form_hatom t_i t_func t_atom)
      (Atom.interp_form_hatom_bv t_i t_func t_atom) _ Hform)
      as [[Hdefault Hwf] _].
    unfold Lit.interp in Htruth.
    rewrite Lit.is_pos_neg, Hsign, Lit.blit_neg in Htruth; simpl in Htruth.
    unfold Var.interp, valuation, EunoiaLocal.valuation in Htruth.
    rewrite Form.wf_interp_form in Htruth by assumption; rewrite Hiff in Htruth.
    change (Bool.eqb (Lit.interp valuation l1) (Lit.interp valuation l2) = true) in Htruth.
    destruct (Lit.interp valuation l1), (Lit.interp valuation l2);
      simpl in Htruth; congruence.
  Qed.


End Tables.
Print Assumptions checker_correct.
Print Assumptions checker_b_correct.
Print Assumptions checker_eq_correct.
End EunoiaCertificate.
