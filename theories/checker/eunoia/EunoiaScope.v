(**************************************************************************)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2026                                          *)
(*     Distributed under the terms of the CeCILL-C licence (see LICENSE). *)
(**************************************************************************)

From Stdlib Require Import List Bool Uint63.
From SMTCoq.utils Require Import PArray.
From SMTCoq.checker.fol Require Import State Terms.
From SMTCoq.checker.eunoia Require Import EunoiaChecker EunoiaBridge.

Import ListNotations EunoiaChecker.
Local Open Scope uint63_scope.
Local Open Scope array_scope.
Set Implicit Arguments.

Module EunoiaScope.

Definition active (rho : Valuation.t) (assumptions : list _lit) : Prop :=
  Forall (fun a => Lit.interp rho a = true) assumptions.

(* Local clauses are justified only when every active assumption holds. *)
Definition invariant (rho : Valuation.t) (assumptions : list _lit)
  (m : machine) : Prop := active rho assumptions -> EunoiaChecker.invariant rho m.

Definition guarded (a : _lit) (c : C.t) : C.t := S.sort (Lit.neg a :: c).

Lemma guarded_valid : forall rho a c,
  Valuation.wf rho ->
  (Lit.interp rho a = true -> C.valid rho c) -> C.valid rho (guarded a c).
Proof.
  intros rho a c Hwf H; unfold guarded, C.valid.
  rewrite S.sort_correct by assumption.
  change (Lit.interp rho (Lit.neg a) || C.interp rho c = true).
  rewrite Lit.interp_neg; destruct (Lit.interp rho a) eqn:Ha; simpl.
  - apply H; reflexivity.
  - reflexivity.
Qed.

Section Generic.
  Context {rule scope_rule witness : Type}.
  Variable eval : rule -> list C.t -> option C.t.
  (* The generated evaluator must check the actual rule's :assumption against
     a, and its sole premise against c. This is deliberately not eval on the
     guarded clause: c is the exact local result, before discharge. *)
  Variable scope_eval : scope_rule -> _lit -> C.t -> option C.t.
  Variable gate : list C.t -> C.t -> witness -> bool.

  Record discharge := Discharge {
    endpoint : clause_id;
    export_slot : clause_id;
    scope_payload : scope_rule;
    scope_conclusion : C.t;
    scope_evidence : witness
  }.

  (* None is an unclosed push, and is rejected. Every ordinary node is checked,
     including nodes after a conflict. A scope retains its parent snapshot. *)
  Inductive trace :=
  | Done
  | Next (st : @step rule witness) (rest : trace)
  | Push (slot : clause_id) (assumption : _lit) (body : trace)
      (closing : option discharge) (rest : trace).

  (* Cache keys only: no inference or clause is removed from checking. *)
  Fixpoint literals (t : trace) : list _lit :=
    match t with
    | Done => []
    | Next st rest => (conclusion st ++ literals rest)%list
    | Push _ a body closing rest =>
      (a :: literals body ++
        (match closing with Some d => scope_conclusion d | None => [] end) ++
        literals rest)%list
    end.

  Definition close (nforms : int) (parent local : machine) (a : _lit)
    (d : discharge) : option machine :=
    match fetch local [endpoint d] with
    | Some [c] =>
      match scope_eval (scope_payload d) a c with
      | Some generated =>
        if clause_eqb generated (scope_conclusion d) &&
           gate [guarded a c] (scope_conclusion d) (scope_evidence d)
        then store nforms parent (export_slot d) (scope_conclusion d)
        else None
      | None => None
      end
    | _ => None
    end.

  Fixpoint run (nforms : int) (m : machine) (t : trace) : option machine :=
    match t with
    | Done => Some m
    | Next st rest =>
      match check_step eval gate nforms m st with
      | Some next => run nforms next rest
      | None => None
      end
    | Push slot a body closing rest =>
      match closing with
      | None => None
      | Some d =>
        match store nforms m slot [a] with
        | None => None
        | Some local =>
          match run nforms local body with
          | None => None
          | Some finished =>
            match close nforms m finished a d with
            | Some next => run nforms next rest
            | None => None
            end
          end
        end
      end
    end.

  Lemma close_binding : forall nforms parent local a d next,
    close nforms parent local a d = Some next -> exists c,
      fetch local [endpoint d] = Some [c] /\
      scope_eval (scope_payload d) a c = Some (scope_conclusion d) /\
      gate [guarded a c] (scope_conclusion d) (scope_evidence d) = true /\
      store nforms parent (export_slot d) (scope_conclusion d) = Some next /\
      S.get (clauses next) (export_slot d) = scope_conclusion d /\
      live next = export_slot d :: live parent.
  Proof.
    intros nforms parent local a d next H; unfold close in H.
    destruct (fetch local [endpoint d]) as [cs|] eqn:Hf; try discriminate.
    destruct cs as [|c [|extra tail]]; try discriminate.
    destruct (scope_eval (scope_payload d) a c) as [generated|] eqn:He;
      try discriminate.
    destruct (clause_eqb generated (scope_conclusion d) &&
      gate [guarded a c] (scope_conclusion d) (scope_evidence d)) eqn:Hg;
      try discriminate.
    apply andb_true_iff in Hg; destruct Hg as [Heq Hg].
    apply clause_eqb_spec in Heq; subst generated.
    destruct (@store_exact nforms parent (export_slot d) (scope_conclusion d)
      next H) as [Hs Hl].
    exists c; repeat split; assumption.
  Qed.

  Lemma close_invariant : forall rho nforms parent local a d next,
    Valuation.wf rho -> gate_sound gate rho ->
    EunoiaChecker.invariant rho parent ->
    (Lit.interp rho a = true -> EunoiaChecker.invariant rho local) ->
    close nforms parent local a d = Some next ->
    EunoiaChecker.invariant rho next.
  Proof.
    intros rho nforms parent local a d next Hwf Hgate Hp Hl H.
    destruct (@close_binding nforms parent local a d next H)
      as [c [Hf [_ [Hg [Hs _]]]]].
    eapply store_invariant; eauto.
    eapply Hgate; eauto; constructor; [|constructor].
    apply guarded_valid; auto; intro Ha.
    pose proof (@fetch_valid rho local [endpoint d] [c] (proj1 (Hl Ha)) Hf)
      as Hc; inversion Hc; assumption.
  Qed.

  Lemma push_invariant : forall rho assumptions nforms m slot a local,
    Valuation.wf rho -> invariant rho assumptions m ->
    store nforms m slot [a] = Some local ->
    invariant rho (a :: assumptions) local.
  Proof.
    intros rho assumptions nforms m slot a local Hwf Hm Hs Hactive.
    inversion Hactive as [|? ? Ha Hrest]; subst.
    eapply store_invariant; eauto.
    unfold C.valid, C.interp; simpl; now rewrite Ha.
  Qed.

  Theorem run_invariant : forall rho assumptions nforms t m next,
    Valuation.wf rho -> gate_sound gate rho -> invariant rho assumptions m ->
    run nforms m t = Some next -> invariant rho assumptions next.
  Proof.
    intros rho assumptions nforms t; revert assumptions.
    induction t as [|st rest IH|slot a body IHbody closing rest IHrest];
      intros assumptions m next Hwf Hgate Hm Hrun; simpl in Hrun.
    - inversion Hrun; subst; assumption.
    - destruct (check_step eval gate nforms m st) as [mid|] eqn:Hs;
        try discriminate.
      apply (IH assumptions mid next Hwf Hgate); auto.
      intros Ha; eapply check_step_invariant; eauto.
    - destruct closing as [d|]; try discriminate.
      destruct (store nforms m slot [a]) as [local|] eqn:Hs; try discriminate.
      destruct (run nforms local body) as [finished|] eqn:Hbody;
        try discriminate.
      destruct (close nforms m finished a d) as [mid|] eqn:Hclose;
        try discriminate.
      assert (invariant rho (a :: assumptions) local) as Hlocal.
      { eapply push_invariant; eauto. }
      pose proof (IHbody _ _ _ Hwf Hgate Hlocal Hbody) as Hfinished.
      apply (IHrest assumptions mid next Hwf Hgate); auto.
      intro Ha; eapply (@close_invariant rho nforms m finished a d mid).
      + exact Hwf.
      + exact Hgate.
      + apply Hm; exact Ha.
      + intro Hlit; apply Hfinished; constructor; assumption.
      + exact Hclose.
  Qed.

  Definition checker (nforms capacity : int) (roots : list C.t)
    (claims : list (clause_id * C.t)) (t : trace) (goal : clause_id) : bool :=
    match load_roots nforms (initial capacity) roots claims with
    | None => false
    | Some m =>
      match run nforms m t with
      | None => false
      | Some next => conflict next goal
      end
    end.

  Theorem checker_correct : forall nforms capacity roots claims t goal rho,
    Valuation.wf rho -> gate_sound gate rho ->
    checker nforms capacity roots claims t goal = true ->
    ~ Forall (C.valid rho) roots.
  Proof.
    intros nforms capacity roots claims t goal rho Hwf Hgate Hcheck Hroots.
    unfold checker in Hcheck.
    destruct (load_roots nforms (initial capacity) roots claims) as [m|] eqn:Hl;
      try discriminate.
    destruct (run nforms m t) as [next|] eqn:Hr; try discriminate.
    assert (invariant rho [] m) as Hm.
    { intros _; eapply load_roots_invariant; eauto; now apply initial_invariant. }
    pose proof (@run_invariant rho [] nforms t m next Hwf Hgate Hm Hr
      (Forall_nil _)) as Hnext.
    unfold conflict in Hcheck; apply andb_true_iff in Hcheck.
    apply (C.is_false_correct _ (proj2 Hcheck) rho).
    apply Hnext.
  Qed.
End Generic.

Section Tables.
  Variable t_i : array CompDec.typ_compdec.
  Variable t_func : array (Atom.tval t_i).
  Variable t_atom : array Atom.atom.
  Variable t_form : array Form.form.
  Context {rule scope_rule : Type}.
  Variable eval : rule -> list C.t -> option C.t.
  Variable scope_eval : scope_rule -> _lit -> C.t -> option C.t.

  (* Unlike the earlier bridge wrapper, this checks Atom.wt at runtime too. *)
  Definition table_checker capacity roots claims
    (t : @trace rule scope_rule EunoiaBridge.witness) goal : bool :=
    Form.check_form t_form && Atom.check_atom t_atom && Atom.wt t_i t_func t_atom &&
    checker eval scope_eval (@EunoiaBridge.gate t_i t_func t_atom t_form)
      (PArray.length t_form) capacity roots claims t goal.

  Theorem table_checker_correct : forall capacity roots claims t goal,
    table_checker capacity roots claims t goal = true ->
    ~ Forall (C.valid (@EunoiaBridge.valuation t_i t_func t_atom t_form)) roots.
  Proof.
    intros capacity roots claims t goal H; unfold table_checker in H.
    rewrite !andb_true_iff in H; destruct H as [[[Hform Hatom] Hwt] Hcheck].
    eapply (@checker_correct rule scope_rule EunoiaBridge.witness eval scope_eval
      (@EunoiaBridge.gate t_i t_func t_atom t_form) (PArray.length t_form)
      capacity roots claims t goal (@EunoiaBridge.valuation t_i t_func t_atom t_form));
      [| |exact Hcheck].
    - exact (proj2 (Form.check_form_correct
        (Atom.interp_form_hatom t_i t_func t_atom)
        (Atom.interp_form_hatom_bv t_i t_func t_atom) t_form Hform)).
    - exact (@EunoiaBridge.gate_correct t_i t_func t_atom t_form Hform Hatom Hwt).
  Qed.

  (* The caller supplies l and b authoritatively; the certificate supplies only
     claims, never an alternative root list. Refute the opposite polarity. *)
  Definition checker_b (l : _lit) (b : bool) capacity claims t goal : bool :=
    table_checker capacity [[if b then Lit.neg l else l]] claims t goal.

  Theorem checker_b_correct : forall l b capacity claims t goal,
    checker_b l b capacity claims t goal = true ->
    Lit.interp (@EunoiaBridge.valuation t_i t_func t_atom t_form) l = b.
  Proof.
    intros l b capacity claims t goal H.
    apply table_checker_correct in H.
    destruct b.
    - destruct (Lit.interp (@EunoiaBridge.valuation t_i t_func t_atom t_form) l)
        eqn:Hl; auto.
      exfalso; apply H; constructor; [|constructor].
      unfold C.valid, C.interp; simpl; now rewrite Lit.interp_neg, Hl.
    - destruct (Lit.interp (@EunoiaBridge.valuation t_i t_func t_atom t_form) l)
        eqn:Hl; auto.
      exfalso; apply H; constructor; [|constructor].
      unfold C.valid, C.interp; simpl; now rewrite Hl.
  Qed.
End Tables.

Print Assumptions guarded_valid.
Print Assumptions close_binding.
Print Assumptions close_invariant.
Print Assumptions push_invariant.
Print Assumptions run_invariant.
Print Assumptions checker_correct.
Print Assumptions table_checker_correct.
Print Assumptions checker_b_correct.

End EunoiaScope.
