(* SMTCoq -- distributed under the CeCILL-C licence (see LICENSE).
   Checked sharing of local certificates; source inferences are never skipped. *)
From Stdlib Require Import List Bool Uint63.
From SMTCoq.utils Require Import PArray CompDec.
From SMTCoq.checker.fol Require Import State Terms.
From SMTCoq.checker.eunoia Require Import EoRuntime CpcGenerated EunoiaChecker
  EunoiaAdapter EunoiaLocal EunoiaScope EunoiaTactic EunoiaScopedAdapter.
Import ListNotations.
Local Open Scope uint63_scope.
Local Open Scope array_scope.
Set Implicit Arguments.
Module EunoiaMemo.

Record cache_entry := CacheEntry {
  cached_premises : list C.t;
  cached_conclusion : C.t;
  cached_witness : EunoiaLocal.witness
}.
Inductive witness_ref := Cached (id : nat) | Inline (w : EunoiaLocal.witness).
Definition trace := @EunoiaScope.trace EunoiaAdapter.rule_payload
  EunoiaAdapter.rule_payload witness_ref.
Definition discharge := @EunoiaScope.discharge EunoiaAdapter.rule_payload witness_ref.
Fixpoint clauses_eqb (a b : list C.t) : bool :=
  match a,b with
  | [],[] => true
  | x::xs,y::ys => EunoiaChecker.clause_eqb x y && clauses_eqb xs ys
  | _,_ => false
  end.
Lemma clauses_eqb_spec : forall a b, clauses_eqb a b = true <-> a = b.
Proof.
  induction a as [|x xs IH]; destruct b as [|y ys]; simpl;
    try (split; [discriminate | congruence]).
  - tauto.
  - rewrite andb_true_iff, EunoiaChecker.clause_eqb_spec, IH.
    split; [intros [-> ->]; reflexivity | intro H; inversion H; auto].
Qed.

Section Tables.
  Variable t_i : array typ_compdec.
  Variable t_func : array (Atom.tval t_i).
  Variable t_atom : array Atom.atom.
  Variable t_form : array Form.form.
  Variable names : EunoiaAdapter.naming.
  Local Notation tables_wf := (EunoiaAdapter.tables_wf t_i t_func t_atom t_form names).
  Local Notation bind_terms := (EunoiaAdapter.bind_terms t_i t_func t_atom t_form names).
  Definition valuation := @EunoiaLocal.valuation t_i t_func t_atom t_form.
  Definition eval_with extra fuel :=
    @EunoiaScopedAdapter.eval_with t_i t_func t_atom t_form names extra fuel.
  Definition scope_eval_with extra fuel :=
    @EunoiaScopedAdapter.scope_eval_with t_i t_func t_atom t_form names extra fuel.
  Definition cache_valid (entries : list cache_entry) :=
    let verify := @EunoiaLocal.gate t_i t_func t_atom t_form in
    forallb (fun e => verify
      (cached_premises e) (cached_conclusion e) (cached_witness e)) entries.
  Definition gate (entries : list cache_entry) : list C.t -> C.t -> witness_ref -> bool :=
    let verify := @EunoiaLocal.gate t_i t_func t_atom t_form in
    fun cs c w =>
    match w with
    | Inline original => verify cs c original
    | Cached id =>
      match nth_error entries id with
      | Some e => clauses_eqb cs (cached_premises e) &&
                  EunoiaChecker.clause_eqb c (cached_conclusion e)
      | None => false
      end
    end.
  Lemma gate_correct : forall entries,
    Atom.wt t_i t_func t_atom = true -> cache_valid entries = true ->
    @EunoiaChecker.gate_sound witness_ref (gate entries) valuation.
  Proof.
    intros entries Hwt Hvalid cs c ref Hgate Hcs.
    destruct ref as [id|original]; [|exact (@EunoiaLocal.gate_correct t_i t_func t_atom t_form Hwt cs c original Hgate Hcs)].
    unfold gate in Hgate.
    destruct (nth_error entries id) as [e|] eqn:He; try discriminate.
    apply andb_true_iff in Hgate; destruct Hgate as [Hprem Hconcl].
    apply clauses_eqb_spec in Hprem; apply EunoiaChecker.clause_eqb_spec in Hconcl.
    subst cs c.
    unfold cache_valid in Hvalid; apply forallb_forall with (x:=e) in Hvalid.
    - eapply (@EunoiaLocal.gate_correct t_i t_func t_atom t_form Hwt); eauto.
    - eapply nth_error_In; eauto.
  Qed.

  Definition checker_with extra fuel entries capacity roots root_terms claims (t : trace) goal :=
    let encodings := EunoiaAdapter.encoding_entries t_i t_func t_atom t_form names fuel
      (List.concat roots ++ EunoiaScope.literals t)%list in
    tables_wf && bind_terms fuel roots root_terms && cache_valid entries &&
    EunoiaScope.checker
      (EunoiaAdapter.cached_eval_with t_i t_func t_atom t_form names encodings
        (CpcGenerated.derive_with extra) fuel)
      (@EunoiaScopedAdapter.cached_scope_eval_with t_i t_func t_atom t_form names
        encodings extra fuel)
      (gate entries) (PArray.length t_form)
      capacity roots claims t goal.
  Definition checker := checker_with CpcGenerated.default_primitive.

  Lemma checker_with_binding : forall extra fuel entries capacity roots root_terms claims t goal,
    checker_with extra fuel entries capacity roots root_terms claims t goal = true ->
    tables_wf = true /\ bind_terms fuel roots root_terms = true /\ cache_valid entries = true.
  Proof.
    intros extra fuel entries capacity roots root_terms claims t goal H.
    unfold checker_with in H; rewrite !andb_true_iff in H; tauto.
  Qed.

  Theorem checker_with_correct : forall extra fuel entries capacity roots root_terms claims t goal,
    checker_with extra fuel entries capacity roots root_terms claims t goal = true ->
    ~ Forall (C.valid valuation) roots.
  Proof.
    intros extra fuel entries capacity roots root_terms claims t goal H.
    pose proof (checker_with_binding _ _ _ _ _ _ _ _ _ H) as [Htables [_ Hcache]].
    unfold EunoiaAdapter.tables_wf in Htables; rewrite !andb_true_iff in Htables.
    destruct Htables as [[[Hnames Hform] Hatom] Hwt].
    unfold checker_with in H; apply andb_true_iff in H; destruct H as [_ H].
    eapply EunoiaScope.checker_correct; [ | | exact H].
    - unfold valuation, EunoiaLocal.valuation.
      apply (proj2 (Form.check_form_correct _ _ _ Hform)).
    - exact (gate_correct entries Hwt Hcache).
  Qed.

  Theorem checker_correct : forall fuel entries capacity roots root_terms claims t goal,
    checker fuel entries capacity roots root_terms claims t goal = true ->
    ~ Forall (C.valid valuation) roots.
  Proof. exact (checker_with_correct CpcGenerated.default_primitive). Qed.

  Definition checker_b_with extra fuel entries capacity l b root_terms claims t goal :=
    checker_with extra fuel entries capacity (EunoiaTactic.goal_roots l b)
      root_terms claims t goal.
  Definition checker_b := checker_b_with CpcGenerated.default_primitive.

  Theorem checker_b_with_correct : forall extra fuel entries capacity l b root_terms claims t goal,
    checker_b_with extra fuel entries capacity l b root_terms claims t goal = true ->
    Lit.interp valuation l = b.
  Proof.
    intros extra fuel entries capacity l b root_terms claims t goal H.
    apply EunoiaTactic.goal_roots_refute; eapply checker_with_correct; exact H.
  Qed.

  Theorem checker_b_correct : forall fuel entries capacity l b root_terms claims t goal,
    checker_b fuel entries capacity l b root_terms claims t goal = true ->
    Lit.interp valuation l = b.
  Proof. exact (checker_b_with_correct CpcGenerated.default_primitive). Qed.

  Definition checker_eq_with extra fuel entries capacity l1 l2 l root_terms claims t goal :=
    if Lit.is_pos l then false else
      match t_form.[Lit.blit l] with
      | Form.Fiff a b => (l1 =? a) && (l2 =? b) &&
        checker_b_with extra fuel entries capacity (Lit.neg l) true root_terms claims t goal
      | _ => false
      end.
  Definition checker_eq := checker_eq_with CpcGenerated.default_primitive.

  Theorem checker_eq_with_correct : forall extra fuel entries capacity l1 l2 l root_terms claims t goal,
    checker_eq_with extra fuel entries capacity l1 l2 l root_terms claims t goal = true ->
    Lit.interp valuation l1 = Lit.interp valuation l2.
  Proof.
    intros extra fuel entries capacity l1 l2 l root_terms claims t goal H.
    unfold checker_eq_with in H.
    destruct (Lit.is_pos l) eqn:Hsign; try discriminate.
    destruct (t_form.[Lit.blit l]) as
      [a| | |n a|ls|ls|ls|a b|a b|a b c|a ls] eqn:Hiff; try discriminate.
    rewrite !andb_true_iff in H; destruct H as [[Ha Hb] Hrun].
    apply Uint63.eqb_spec in Ha; apply Uint63.eqb_spec in Hb; subst a b.
    pose proof (checker_b_with_correct _ _ _ _ _ _ _ _ _ _ Hrun) as Htruth.
    pose proof (checker_with_binding _ _ _ _ _ _ _ _ _ Hrun) as [Htables [_ Hcache]].
    unfold EunoiaAdapter.tables_wf in Htables; rewrite !andb_true_iff in Htables.
    destruct Htables as [[[Hnames Hform] Hatom] Hwt].
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

  Theorem checker_eq_correct : forall fuel entries capacity l1 l2 l root_terms claims t goal,
    checker_eq fuel entries capacity l1 l2 l root_terms claims t goal = true ->
    Lit.interp valuation l1 = Lit.interp valuation l2.
  Proof. exact (checker_eq_with_correct CpcGenerated.default_primitive). Qed.
End Tables.
End EunoiaMemo.
Print Assumptions EunoiaMemo.gate_correct.
Print Assumptions EunoiaMemo.checker_correct.
Print Assumptions EunoiaMemo.checker_b_correct.
Print Assumptions EunoiaMemo.checker_eq_correct.
