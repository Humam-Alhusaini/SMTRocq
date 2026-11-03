(**************************************************************************)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2026                                          *)
(*     Distributed under the terms of the CeCILL-C licence (see LICENSE). *)
(**************************************************************************)

From Stdlib Require Import List Bool Uint63.
From SMTCoq.utils Require Import PArray.
From SMTCoq.structures Require Import CompDecInstances.
From SMTCoq.checker.fol Require Import State Terms.
From SMTCoq.checker Require Import MainChecker.
From SMTCoq.checker.eunoia Require Import EunoiaChecker EunoiaLocal.

Import ListNotations EunoiaChecker.
Local Open Scope uint63_scope.
Local Open Scope array_scope.
Set Implicit Arguments.

Module EunoiaBridge.

Fixpoint clauses_eqb (xs ys : list C.t) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs, y :: ys => clause_eqb x y && clauses_eqb xs ys
  | _, _ => false
  end.

Lemma clauses_eqb_spec : forall xs ys, clauses_eqb xs ys = true <-> xs = ys.
Proof.
  induction xs as [ |x xs IH]; destruct ys as [ |y ys]; simpl;
    try (split; [discriminate | congruence]).
  - tauto.
  - rewrite andb_true_iff, clause_eqb_spec, IH.
    split; [intros [-> ->]; reflexivity | intro H; inversion H; auto].
Qed.

(* This is the existing small-checker witness language, not generated CPC syntax.
   Its indices are local scratch-state indices, not global proof-state indices. *)
Record witness := Witness {
  scratch_capacity : int;
  action : Checker_Ext.step
}.

Section Context.
  Variable t_i : array CompDec.typ_compdec.
  Variable t_func : array (Atom.tval t_i).
  Variable t_atom : array Atom.atom.
  Variable t_form : array Form.form.

  Definition valuation : Valuation.t :=
    Form.interp_state_var (Atom.interp_form_hatom t_i t_func t_atom)
      (Atom.interp_form_hatom_bv t_i t_func t_atom) t_form.

  Record plan := Plan {
    reads : list clause_id;
    output : clause_id;
    literals : list _lit;
    semantic_step : @Euf_Checker.step t_i t_func t_atom t_form
  }.

  (* Reuse the production operation decoder, including literal references and
     its binary-resolution restriction. A longer chain must expose each link. *)
  Definition decode (w : Checker_Ext.step) : option plan :=
    match @EunoiaLocal.decode t_i t_func t_atom t_form w with
    | None => None
    | Some p => Some (Plan (EunoiaLocal.reads p) (EunoiaLocal.output p)
        (EunoiaLocal.literals p) (EunoiaLocal.semantic_step p))
    end.

  (* Construct a fresh scratch state using exactly the supplied premises. Check
     the readback explicitly: combine must not hide an extra or missing read. *)
  Definition prepare (cs : list C.t) (w : witness) : option (machine * plan) :=
    match decode (action w) with
    | None => None
    | Some p =>
      match load_roots (PArray.length t_form) (initial (scratch_capacity w))
              cs (combine (reads p) cs) with
      | None => None
      | Some m =>
        match fetch m (reads p) with
        | None => None
        | Some bound =>
          if clauses_eqb bound cs &&
             (output p <? PArray.length (clauses m)) &&
             negb (existsb (fun id => output p =? id) (live m))
          then Some (m, p) else None
        end
      end
    end.

  Definition gate (cs : list C.t) (c : C.t) (w : witness) : bool :=
    match prepare cs w with
    | None => false
    | Some (m, p) =>
      let result := S.get
        (Euf_Checker.step_checker (clauses m) (semantic_step p)) (output p) in
      clause_wf (PArray.length t_form) c &&
      forallb (fun l => Lit.blit l <? PArray.length t_form) (literals p) &&
      EunoiaLocal.result_supported (action w) result && clause_eqb result c
    end.

  Lemma prepare_binding : forall cs w m p,
    prepare cs w = Some (m, p) ->
    decode (action w) = Some p /\
    load_roots (PArray.length t_form) (initial (scratch_capacity w))
      cs (combine (reads p) cs) = Some m /\
    fetch m (reads p) = Some cs /\
    (output p <? PArray.length (clauses m)) = true /\
    ~ In (output p) (live m).
  Proof.
    intros cs w m p H; unfold prepare in H.
    destruct (decode (action w)) as [p'| ] eqn:Hd; try discriminate.
    destruct (load_roots (PArray.length t_form) (initial (scratch_capacity w))
      cs (combine (reads p') cs)) as [m'| ] eqn:Hl; try discriminate.
    destruct (fetch m' (reads p')) as [bound| ] eqn:Hf; try discriminate.
    destruct (clauses_eqb bound cs && (output p' <? PArray.length (clauses m')) &&
      negb (existsb (fun id => output p' =? id) (live m'))) eqn:Hg;
      try discriminate.
    inversion H; subst p' m'; clear H.
    rewrite !andb_true_iff in Hg; destruct Hg as [[Heq Hb] Hfresh].
    apply clauses_eqb_spec in Heq; subst bound.
    repeat split; auto.
    intro Hin; apply negb_true_iff in Hfresh.
    assert (existsb (fun id => output p =? id) (live m) = true) as Hex.
    { apply existsb_exists; exists (output p); split; auto; apply Uint63.eqb_refl. }
    congruence.
  Qed.

  Lemma gate_binding : forall cs c w,
    gate cs c w = true -> exists m p,
      prepare cs w = Some (m, p) /\
      decode (action w) = Some p /\
      load_roots (PArray.length t_form) (initial (scratch_capacity w))
        cs (combine (reads p) cs) = Some m /\
      fetch m (reads p) = Some cs /\
      S.get (Euf_Checker.step_checker (clauses m) (semantic_step p)) (output p) = c /\
      (output p <? PArray.length (clauses m)) = true /\
      ~ In (output p) (live m).
  Proof.
    intros cs c w H; unfold gate in H.
    destruct (prepare cs w) as [[m p]| ] eqn:Hp; try discriminate.
    apply andb_true_iff in H as [_ H].
    apply clause_eqb_spec in H.
    destruct (@prepare_binding cs w m p Hp) as [Hd [Hl [Hf [Hb Hfresh]]]].
    exists m, p; repeat split; assumption.
  Qed.

  (* The only semantic justification is the existing SMTCoq checker theorem.
     The local state has no roots beyond cs, and only one witness step runs. *)
  Theorem gate_correct :
    Form.check_form t_form = true -> Atom.check_atom t_atom = true ->
    Atom.wt t_i t_func t_atom -> gate_sound gate valuation.
  Proof.
    intros Hform Hatom Hwt cs c w Hgate Hcs; unfold gate in Hgate.
    destruct (prepare cs w) as [[m p]| ] eqn:Hp; try discriminate.
    destruct (@prepare_binding cs w m p Hp) as [_ [Hl _]].
    assert (Valuation.wf valuation) as Hwf.
    { unfold valuation; apply (proj2 (Form.check_form_correct _ _ _ Hform)). }
    assert (invariant valuation m) as Hm.
    { eapply load_roots_invariant; eauto; now apply initial_invariant. }
    apply andb_true_iff in Hgate as [_ Hgate].
    apply clause_eqb_spec in Hgate; rewrite <- Hgate.
    apply (Euf_Checker.step_checker_correct Hform Hatom Hwt).
    apply Hm.
  Qed.

  Definition checker {rule : Type} (eval : rule -> list C.t -> option C.t)
    capacity roots claims (trace : list (@step rule witness)) goal : bool :=
    Form.check_form t_form && Atom.check_atom t_atom &&
    EunoiaChecker.checker eval gate (PArray.length t_form)
      capacity roots claims trace goal.

  Theorem checker_correct : forall (rule : Type) eval capacity roots claims
    (trace : list (@step rule witness)) goal,
    Atom.wt t_i t_func t_atom ->
    checker eval capacity roots claims trace goal = true ->
    ~ Forall (C.valid valuation) roots.
  Proof.
    intros rule eval capacity roots claims trace goal Hwt H.
    unfold checker in H; rewrite !andb_true_iff in H.
    destruct H as [[Hform Hatom] Hcheck].
    eapply EunoiaChecker.checker_correct; eauto.
    - unfold valuation; apply (proj2 (Form.check_form_correct _ _ _ Hform)).
    - now apply gate_correct.
  Qed.
End Context.

Print Assumptions clauses_eqb_spec.
Print Assumptions prepare_binding.
Print Assumptions gate_binding.
Print Assumptions gate_correct.
Print Assumptions checker_correct.

End EunoiaBridge.
