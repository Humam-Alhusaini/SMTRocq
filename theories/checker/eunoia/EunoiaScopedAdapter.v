(**************************************************************************)
(*     SMTCoq -- distributed under the terms of the CeCILL-C licence       *)
(**************************************************************************)

From Stdlib Require Import List String Bool Uint63.
From SMTCoq.utils Require Import PArray CompDec.
From SMTCoq.checker.fol Require Import State Terms.
From SMTCoq.checker.eunoia Require Import
  EoSyntax EoRuntime CpcGenerated EunoiaChecker EunoiaAdapter EunoiaLocal
  EunoiaScope EunoiaTactic.

Import ListNotations.
Local Open Scope uint63_scope.
Local Open Scope array_scope.
Set Implicit Arguments.

Module EunoiaScopedAdapter.

(* Both ordinary and closing nodes retain the source rule's exact arguments,
   ordered premise terms, result term and result clause. No rule-name switch. *)
Definition trace := @EunoiaScope.trace EunoiaAdapter.rule_payload
  EunoiaAdapter.rule_payload EunoiaLocal.witness.
Definition discharge := @EunoiaScope.discharge EunoiaAdapter.rule_payload
  EunoiaLocal.witness.

Section Tables.
  Variable t_i : array typ_compdec.
  Variable t_func : array (Atom.tval t_i).
  Variable t_atom : array Atom.atom.
  Variable t_form : array Form.form.
  Variable names : EunoiaAdapter.naming.

  Local Notation tables_wf := (EunoiaAdapter.tables_wf t_i t_func t_atom t_form names).
  Local Notation bind_terms := (EunoiaAdapter.bind_terms t_i t_func t_atom t_form names).
  Local Notation binds := (EunoiaAdapter.binds t_i t_func t_atom t_form names).
  Local Notation encode_literal := (EunoiaAdapter.encode_literal t_i t_func t_atom t_form names).
  Local Notation typeof := (EunoiaAdapter.typeof t_i t_func names).

  Definition valuation := @EunoiaLocal.valuation t_i t_func t_atom t_form.

  (* Extensions are language primitives fixed by the backend, never a rule
     evaluator or a field of the proof. Every call still runs CpcGenerated. *)
  Definition eval_with (extra : EoRuntime.primitive_hook) :=
    EunoiaAdapter.eval_with t_i t_func t_atom t_form names
      (CpcGenerated.derive_with extra).
  Definition eval := eval_with CpcGenerated.default_primitive.

  (* Source syntax is retained across lowering (including purification).
     It must bind to the actual pushed literal before generated discharge. *)
  Definition scope_assumption fuel (p : EunoiaAdapter.rule_payload) a :=
    match EunoiaAdapter.source_assumption p with
    | Some raw => if binds fuel [a] raw then Some raw else None
    | None => encode_literal fuel a
    end.

  Lemma scope_assumption_binding : forall fuel p a raw,
    scope_assumption fuel p a = Some raw ->
    (EunoiaAdapter.source_assumption p = Some raw /\ binds fuel [a] raw = true) \/
    (EunoiaAdapter.source_assumption p = None /\ encode_literal fuel a = Some raw).
  Proof.
    intros fuel p a raw H; unfold scope_assumption in H.
    destruct (EunoiaAdapter.source_assumption p) as [source|] eqn:Hs.
    - destruct (binds fuel [a] source) eqn:Hb; try discriminate.
      inversion H; subst; left; auto.
    - right; auto.
  Qed.

  Definition scope_eval_with (extra : EoRuntime.primitive_hook) (fuel : nat) :=
    let tables_ready := tables_wf in
    fun (p : EunoiaAdapter.rule_payload) (a : _lit) (c : C.t) =>
    if tables_ready && bind_terms fuel [c] (EunoiaAdapter.premise_terms p) then
      match scope_assumption fuel p a with
      | None => None
      | Some pushed =>
        match CpcGenerated.derive_assuming_with extra fuel (typeof fuel)
          (EunoiaAdapter.rule_name p) pushed (EunoiaAdapter.arguments p)
          (EunoiaAdapter.premise_terms p) with
        | None => None
        | Some result =>
          if term_eqb result (EunoiaAdapter.result_term p) &&
             binds fuel (EunoiaAdapter.result_clause p) result
          then Some (EunoiaAdapter.result_clause p) else None
        end
      end
    else None.
  Definition scope_eval := scope_eval_with CpcGenerated.default_primitive.

  Lemma scope_eval_with_binding : forall extra fuel p a c result,
    scope_eval_with extra fuel p a c = Some result ->
    tables_wf = true /\
    bind_terms fuel [c] (EunoiaAdapter.premise_terms p) = true /\
    exists pushed,
      scope_assumption fuel p a = Some pushed /\
      CpcGenerated.derive_assuming_with extra fuel (typeof fuel)
        (EunoiaAdapter.rule_name p) pushed (EunoiaAdapter.arguments p)
        (EunoiaAdapter.premise_terms p) = Some (EunoiaAdapter.result_term p) /\
      binds fuel result (EunoiaAdapter.result_term p) = true /\
      result = EunoiaAdapter.result_clause p.
  Proof.
    intros extra fuel p a c result H; unfold scope_eval_with in H.
    destruct (tables_wf && bind_terms fuel [c] (EunoiaAdapter.premise_terms p))
      eqn:Hg; try discriminate.
    destruct (scope_assumption fuel p a) as [pushed|] eqn:Ha; try discriminate.
    destruct (CpcGenerated.derive_assuming_with extra fuel (typeof fuel)
      (EunoiaAdapter.rule_name p) pushed (EunoiaAdapter.arguments p)
      (EunoiaAdapter.premise_terms p)) as [generated|] eqn:Hd; try discriminate.
    destruct (term_eqb generated (EunoiaAdapter.result_term p) &&
      binds fuel (EunoiaAdapter.result_clause p) generated) eqn:Hb; try discriminate.
    inversion H; subst result; clear H.
    apply andb_true_iff in Hg; destruct Hg as [Hw Hp].
    apply andb_true_iff in Hb; destruct Hb as [He Hb].
    apply EunoiaAdapter.term_eqb_spec in He; subst generated.
    repeat split; auto; exists pushed; auto.
  Qed.

  Definition run_with extra fuel := EunoiaScope.run (eval_with extra fuel)
    (scope_eval_with extra fuel) (@EunoiaLocal.gate t_i t_func t_atom t_form)
    (PArray.length t_form).
  Definition run := run_with CpcGenerated.default_primitive.

  (* This strengthens close_binding with the concrete generated boundary. The
     endpoint is c, never guarded a c; only the semantic gate sees the guard. *)
  Lemma close_with_binding : forall extra fuel parent local a (d : discharge) next,
    EunoiaScope.close (scope_eval_with extra fuel)
      (@EunoiaLocal.gate t_i t_func t_atom t_form) (PArray.length t_form)
      parent local a d = Some next ->
    exists c pushed,
      EunoiaChecker.fetch local [EunoiaScope.endpoint d] = Some [c] /\
      scope_assumption fuel (EunoiaScope.scope_payload d) a = Some pushed /\
      bind_terms fuel [c]
        (EunoiaAdapter.premise_terms (EunoiaScope.scope_payload d)) = true /\
      CpcGenerated.derive_assuming_with extra fuel (typeof fuel)
        (EunoiaAdapter.rule_name (EunoiaScope.scope_payload d)) pushed
        (EunoiaAdapter.arguments (EunoiaScope.scope_payload d))
        (EunoiaAdapter.premise_terms (EunoiaScope.scope_payload d)) =
        Some (EunoiaAdapter.result_term (EunoiaScope.scope_payload d)) /\
      binds fuel (EunoiaScope.scope_conclusion d)
        (EunoiaAdapter.result_term (EunoiaScope.scope_payload d)) = true /\
      @EunoiaLocal.gate t_i t_func t_atom t_form [EunoiaScope.guarded a c]
        (EunoiaScope.scope_conclusion d) (EunoiaScope.scope_evidence d) = true /\
      EunoiaChecker.store (PArray.length t_form) parent (EunoiaScope.export_slot d)
        (EunoiaScope.scope_conclusion d) = Some next /\
      S.get (EunoiaChecker.clauses next) (EunoiaScope.export_slot d) =
        EunoiaScope.scope_conclusion d /\
      EunoiaChecker.live next = EunoiaScope.export_slot d :: EunoiaChecker.live parent.
  Proof.
    intros extra fuel parent local a d next H.
    apply EunoiaScope.close_binding in H.
    destruct H as [c [Hfetch [Heval [Hgate [Hstore [Hread Hlive]]]]]].
    apply scope_eval_with_binding in Heval.
    destruct Heval as [_ [Hprem [pushed [Hpush [Hderive [Hbind _]]]]]].
    exists c, pushed; repeat split; assumption.
  Qed.

  Definition checker_with extra fuel capacity roots root_terms claims (t : trace) goal :=
    tables_wf && bind_terms fuel roots root_terms &&
    EunoiaScope.checker (eval_with extra fuel) (scope_eval_with extra fuel)
      (@EunoiaLocal.gate t_i t_func t_atom t_form) (PArray.length t_form)
      capacity roots claims t goal.
  Definition checker := checker_with CpcGenerated.default_primitive.

  Lemma checker_with_binding : forall extra fuel capacity roots root_terms claims t goal,
    checker_with extra fuel capacity roots root_terms claims t goal = true ->
    tables_wf = true /\ bind_terms fuel roots root_terms = true.
  Proof.
    intros extra fuel capacity roots root_terms claims t goal H.
    unfold checker_with in H; rewrite !andb_true_iff in H; tauto.
  Qed.

  Theorem checker_with_correct : forall extra fuel capacity roots root_terms claims t goal,
    checker_with extra fuel capacity roots root_terms claims t goal = true ->
    ~ Forall (C.valid valuation) roots.
  Proof.
    intros extra fuel capacity roots root_terms claims t goal H.
    pose proof (checker_with_binding _ _ _ _ _ _ _ _ H) as [Htables _].
    unfold EunoiaAdapter.tables_wf in Htables; rewrite !andb_true_iff in Htables.
    destruct Htables as [[[Hnames Hform] Hatom] Hwt].
    unfold checker_with in H; apply andb_true_iff in H; destruct H as [_ H].
    eapply EunoiaScope.checker_correct; [ | | exact H].
    - unfold valuation, EunoiaLocal.valuation.
      apply (proj2 (Form.check_form_correct _ _ _ Hform)).
    - exact (@EunoiaLocal.gate_correct t_i t_func t_atom t_form Hwt).
  Qed.

  Theorem checker_correct : forall fuel capacity roots root_terms claims t goal,
    checker fuel capacity roots root_terms claims t goal = true ->
    ~ Forall (C.valid valuation) roots.
  Proof. exact (checker_with_correct CpcGenerated.default_primitive). Qed.

  Definition checker_b_with extra fuel capacity l b root_terms claims t goal :=
    checker_with extra fuel capacity (EunoiaTactic.goal_roots l b)
      root_terms claims t goal.
  Definition checker_b := checker_b_with CpcGenerated.default_primitive.

  Theorem checker_b_with_correct : forall extra fuel capacity l b root_terms claims t goal,
    checker_b_with extra fuel capacity l b root_terms claims t goal = true ->
    Lit.interp valuation l = b.
  Proof.
    intros extra fuel capacity l b root_terms claims t goal H.
    apply EunoiaTactic.goal_roots_refute; eapply checker_with_correct; exact H.
  Qed.

  Theorem checker_b_correct : forall fuel capacity l b root_terms claims t goal,
    checker_b fuel capacity l b root_terms claims t goal = true ->
    Lit.interp valuation l = b.
  Proof. exact (checker_b_with_correct CpcGenerated.default_primitive). Qed.

  Definition checker_eq_with extra fuel capacity l1 l2 l root_terms claims t goal :=
    if Lit.is_pos l then false else
      match t_form.[Lit.blit l] with
      | Form.Fiff a b => (l1 =? a) && (l2 =? b) &&
        checker_b_with extra fuel capacity (Lit.neg l) true root_terms claims t goal
      | _ => false
      end.
  Definition checker_eq := checker_eq_with CpcGenerated.default_primitive.

  Theorem checker_eq_with_correct : forall extra fuel capacity l1 l2 l root_terms claims t goal,
    checker_eq_with extra fuel capacity l1 l2 l root_terms claims t goal = true ->
    Lit.interp valuation l1 = Lit.interp valuation l2.
  Proof.
    intros extra fuel capacity l1 l2 l root_terms claims t goal H.
    unfold checker_eq_with in H.
    destruct (Lit.is_pos l) eqn:Hsign; try discriminate.
    destruct (t_form.[Lit.blit l]) as
      [a| | |n a|ls|ls|ls|a b|a b|a b c|a ls] eqn:Hiff; try discriminate.
    rewrite !andb_true_iff in H; destruct H as [[Ha Hb] Hrun].
    apply Uint63.eqb_spec in Ha; apply Uint63.eqb_spec in Hb; subst a b.
    pose proof (checker_b_with_correct _ _ _ _ _ _ _ _ _ Hrun) as Htruth.
    pose proof (checker_with_binding _ _ _ _ _ _ _ _ Hrun) as [Htables _].
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

  Theorem checker_eq_correct : forall fuel capacity l1 l2 l root_terms claims t goal,
    checker_eq fuel capacity l1 l2 l root_terms claims t goal = true ->
    Lit.interp valuation l1 = Lit.interp valuation l2.
  Proof. exact (checker_eq_with_correct CpcGenerated.default_primitive). Qed.
End Tables.

Print Assumptions scope_eval_with_binding.
Print Assumptions scope_assumption_binding.
Print Assumptions close_with_binding.
Print Assumptions checker_with_binding.
Print Assumptions checker_with_correct.
Print Assumptions checker_correct.
Print Assumptions checker_b_with_correct.
Print Assumptions checker_b_correct.
Print Assumptions checker_eq_with_correct.
Print Assumptions checker_eq_correct.

End EunoiaScopedAdapter.
