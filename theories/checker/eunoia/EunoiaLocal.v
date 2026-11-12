(**************************************************************************)
(*     SMTCoq -- distributed under the terms of the CeCILL-C licence       *)
(**************************************************************************)

From Stdlib Require Import List Bool Uint63.
From SMTCoq.utils Require Import Misc PArray.
From SMTCoq.checker.fol Require Import State Terms.
From SMTCoq.checker Require Import MainChecker.
From SMTCoq.checker.small_checker.array Require Import Array.
From SMTCoq.checker.eunoia Require Import EunoiaBool.

Import ListNotations.
Local Open Scope uint63_scope.
Local Open Scope array_scope.
Set Implicit Arguments.

Module EunoiaLocal.

(* This module does not depend on the generated CPC syntax or the global proof
   state. Each invocation certifies just cs ==> c, after generated derivation
   and exact binding have been checked independently by the caller. *)
Fixpoint clause_eqb (a b : C.t) : bool :=
  match a, b with
  | [], [] => true
  | x :: xs, y :: ys => (x =? y) && clause_eqb xs ys
  | _, _ => false
  end.

Lemma clause_eqb_spec : forall a b, clause_eqb a b = true <-> a = b.
Proof.
  induction a as [ |x xs IH]; destruct b as [ |y ys]; simpl;
    try (split; [discriminate | congruence]).
  - tauto.
  - rewrite andb_true_iff, Uint63.eqb_spec, IH.
    split; [intros [-> ->]; reflexivity | intro H; inversion H; auto].
Qed.

Definition clause_wf (nforms : int) (c : C.t) : bool :=
  forallb (fun l => Lit.blit l <? nforms) c && clause_eqb (S.sort c) c.

Record machine := Machine { clauses : S.t; live : list clause_id }.
Definition initial capacity := Machine (S.make capacity) [].
Definition available m id :=
  (id <? PArray.length (clauses m)) && existsb (fun j => id =? j) (live m).
Definition fresh m id :=
  (id <? PArray.length (clauses m)) &&
  negb (existsb (fun j => id =? j) (live m)).

Lemma available_spec : forall m id, available m id = true <->
  (id <? PArray.length (clauses m)) = true /\ In id (live m).
Proof.
  intros m id; unfold available; rewrite andb_true_iff, existsb_exists.
  split.
  - intros [Hb [j [Hj Heq]]]; apply Uint63.eqb_spec in Heq; subst; auto.
  - intros [Hb Hi]; split; auto; exists id; split; auto.
    apply Uint63.eqb_refl.
Qed.

Lemma fresh_spec : forall m id, fresh m id = true <->
  (id <? PArray.length (clauses m)) = true /\ ~ In id (live m).
Proof.
  intros m id; unfold fresh.
  rewrite andb_true_iff, negb_true_iff.
  split.
  - intros [Hb Hfresh]; split; auto; intro Hin.
    assert (existsb (fun j => id =? j) (live m) = true) as H.
    { apply existsb_exists; exists id; split; auto; apply Uint63.eqb_refl. }
    congruence.
  - intros [Hb Hfresh]; split; auto.
    destruct (existsb (fun j => id =? j) (live m)) eqn:H; auto.
    apply existsb_exists in H; destruct H as [j [Hj Heq]].
    apply Uint63.eqb_spec in Heq; subst; contradiction.
Qed.

(* Negate a clause as a conjunction of units; NEVER split premise clauses.
   In particular c=[] adds no roots, and c=[l] adds exactly [neg l]. *)
Definition local_roots (cs : list C.t) (c : C.t) : list C.t :=
  cs ++ map (fun l => [Lit.neg l]) c.

Fixpoint load_roots nforms (m : machine) (roots : list C.t)
  (claims : list (clause_id * C.t)) : option machine :=
  match roots, claims with
  | [], [] => Some m
  | c :: roots, (id, claimed) :: claims =>
    if clause_eqb c claimed && clause_wf nforms c && fresh m id then
      load_roots nforms (Machine (S.set_clause (clauses m) id c) (id :: live m))
        roots claims
    else None
  | _, _ => None
  end.

Lemma load_roots_binding : forall nforms roots claims m m',
  load_roots nforms m roots claims = Some m' -> map snd claims = roots.
Proof.
  intros nforms roots; induction roots as [ |c roots IH];
    intros claims m m' H; destruct claims as [ |[id claimed] claims];
    simpl in H; try discriminate; [reflexivity| ].
  destruct (clause_eqb c claimed && clause_wf nforms c && fresh m id)
    eqn:Hg; try discriminate.
  rewrite !andb_true_iff in Hg; destruct Hg as [[Heq _] _].
  apply clause_eqb_spec in Heq; subst claimed; simpl; f_equal; eapply IH; eauto.
Qed.

Lemma load_roots_valid : forall rho nforms roots claims m m',
  Valuation.wf rho -> Forall (C.valid rho) roots -> S.valid rho (clauses m) ->
  load_roots nforms m roots claims = Some m' -> S.valid rho (clauses m').
Proof.
  intros rho nforms roots; induction roots as [ |c roots IH];
    intros claims m m' Hwf Hr Hm H; destruct claims as [ |[id claimed] claims];
    simpl in H; try discriminate.
  - inversion H; subst; assumption.
  - destruct (clause_eqb c claimed && clause_wf nforms c && fresh m id);
      try discriminate.
    inversion Hr; subst.
    eapply (IH claims (Machine (S.set_clause (clauses m) id c) (id :: live m))
      m'); eauto.
    simpl; now apply S.valid_set_clause.
Qed.

Lemma local_roots_valid : forall rho cs c,
  Forall (C.valid rho) cs -> C.interp rho c = false ->
  Forall (C.valid rho) (local_roots cs c).
Proof.
  intros rho cs c Hcs Hc; unfold local_roots; apply Forall_app; split; auto.
  clear cs Hcs; induction c as [ |l c IH]; simpl in *; [constructor| ].
  apply orb_false_iff in Hc; destruct Hc as [Hl Hc].
  constructor; auto.
  unfold C.valid; change (Lit.interp rho (Lit.neg l) || false = true).
  now rewrite Lit.interp_neg, Hl.
Qed.

(* No proof-valued constructors exist in this witness language. The raw core
   array/BV shapes remain rejected by decode. Array rules below have their own
   canonicalizing path through the existing verified array small checkers.
   Every accepted operation explicitly enumerates ALL its local clause reads. *)
Inductive array_rule :=
| ArrayReadSame (res : _lit)
| ArrayReadOther (clause : C.t)
| ArrayExtensionality (res : _lit).
Definition array_literals r :=
  match r with ArrayReadSame l | ArrayExtensionality l => [l]
  | ArrayReadOther c => c end.
Inductive command :=
| Command (a : Checker_Ext.step) (expected : C.t)
| BoolCongrCommand (pos : clause_id) (res : _lit)
    (eqs : list (option _lit)) (expected : C.t)
| ArrayCommand (pos : clause_id) (rule : array_rule) (expected : C.t).

(* Preserve the old constructor, with an honest optional core projection. *)
Definition action (cmd : command) : option Checker_Ext.step :=
  match cmd with Command a _ => Some a | _ => None end.
Definition expected (cmd : command) : C.t :=
  match cmd with Command _ c | BoolCongrCommand _ _ _ c | ArrayCommand _ _ c => c end.
Record witness := Witness {
  capacity : int;
  root_claims : list (clause_id * C.t);
  program : list command;
  conflict : clause_id
}.

(* A dedicated CTrue operation has a proved successful singleton-true result.
   Every other operation must still distinguish its result from the failure
   fallback, even when the requested conclusion is itself a tautology. *)
Definition result_supported (a : Checker_Ext.step) (c : C.t) : bool :=
  match a with
  | Checker_Ext.CTrue _ => clause_eqb c C._true
  | _ => negb (clause_eqb c C._true)
  end.

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

  Definition option_literals (ls : list (option _lit)) : list _lit :=
    flat_map (fun x => match x with Some l => [l] | None => [] end) ls.

  Definition decode (a : Checker_Ext.step) : option plan :=
    match a with
    | Checker_Ext.Res pos r =>
      (* Binary resolution makes a fallback at ANY link observable. Longer
         chains must be expressed as several fresh binary operations. *)
      if PArray.length r =? 2 then
        Some (Plan (to_list r) pos [] (@Euf_Checker.Res _ _ _ _ pos r))
      else None
    | Checker_Ext.Weaken pos id c =>
      Some (Plan [id] pos c (@Euf_Checker.Weaken _ _ _ _ pos id c))
    | Checker_Ext.ImmFlatten pos id l =>
      Some (Plan [id] pos [l] (@Euf_Checker.ImmFlatten _ _ _ _ pos id l))
    | Checker_Ext.CFalse pos =>
      Some (Plan [] pos [] (@Euf_Checker.CFalse _ _ _ _ pos))
    | Checker_Ext.CTrue pos =>
      Some (Plan [] pos [] (@Euf_Checker.CTrue _ _ _ _ pos))
    | Checker_Ext.BuildDef pos l =>
      Some (Plan [] pos [l] (@Euf_Checker.BuildDef _ _ _ _ pos l))
    | Checker_Ext.BuildDef2 pos l =>
      Some (Plan [] pos [l] (@Euf_Checker.BuildDef2 _ _ _ _ pos l))
    | Checker_Ext.BuildProj pos l i =>
      Some (Plan [] pos [l] (@Euf_Checker.BuildProj _ _ _ _ pos l i))
    | Checker_Ext.ImmBuildDef pos id =>
      Some (Plan [id] pos [] (@Euf_Checker.ImmBuildDef _ _ _ _ pos id))
    | Checker_Ext.ImmBuildDef2 pos id =>
      Some (Plan [id] pos [] (@Euf_Checker.ImmBuildDef2 _ _ _ _ pos id))
    | Checker_Ext.ImmBuildProj pos id i =>
      Some (Plan [id] pos [] (@Euf_Checker.ImmBuildProj _ _ _ _ pos id i))
    | Checker_Ext.EqTr pos l ls =>
      Some (Plan [] pos (l :: ls) (@Euf_Checker.EqTr _ _ _ _ pos l ls))
    | Checker_Ext.EqCgr pos l ls =>
      Some (Plan [] pos (l :: option_literals ls)
        (@Euf_Checker.EqCgr _ _ _ _ pos l ls))
    | Checker_Ext.EqCgrP pos l1 l2 ls =>
      Some (Plan [] pos (l1 :: l2 :: option_literals ls)
        (@Euf_Checker.EqCgrP _ _ _ _ pos l1 l2 ls))
    | Checker_Ext.LiaMicromega pos c proof =>
      Some (Plan [] pos c (@Euf_Checker.LiaMicromega _ _ _ _ pos c proof))
    | Checker_Ext.LiaDiseq pos l =>
      Some (Plan [] pos [l] (@Euf_Checker.LiaDiseq _ _ _ _ pos l))
    | Checker_Ext.SplArith pos id l proof =>
      Some (Plan [id] pos [l] (@Euf_Checker.SplArith _ _ _ _ pos id l proof))
    | Checker_Ext.SplDistinctElim pos id l =>
      Some (Plan [id] pos [l] (@Euf_Checker.SplDistinctElim _ _ _ _ pos id l))
    | _ => None
    end.

  Definition execute_core (m : machine) (a : Checker_Ext.step) (expected : C.t) : option machine :=
    match decode a with
    | None => None
    | Some p =>
      if forallb (available m) (reads p) && fresh m (output p) &&
         forallb (fun l => Lit.blit l <? PArray.length t_form) (literals p)
      then
        let s' := Euf_Checker.step_checker (clauses m) (semantic_step p) in
        let result := S.get s' (output p) in
        if clause_wf (PArray.length t_form) expected &&
           clause_eqb result expected && result_supported a result
        then Some (Machine s' (output p :: live m)) else None
      else None
    end.

  Definition execute_bool (m : machine) (pos : clause_id) (res : _lit)
      (eqs : list (option _lit)) (expected : C.t) : option machine :=
    if fresh m pos &&
       forallb (fun l => Lit.blit l <? PArray.length t_form)
         (res :: option_literals eqs) then
      match EunoiaBool.congr_clause t_i t_func t_atom t_form res eqs with
      | None => None
      | Some raw_clause =>
        let s' := S.set_clause (clauses m) pos raw_clause in
        let result := S.get s' pos in
        if clause_wf (PArray.length t_form) expected &&
           clause_eqb result expected && negb (clause_eqb result C._true)
        then Some (Machine s' (pos :: live m)) else None
      end
    else None.

  Definition array_clause rule :=
    match rule with
    | ArrayReadSame l => check_roweq t_form t_atom l
    | ArrayReadOther c => check_rowneq t_form t_atom c
    | ArrayExtensionality l => check_ext t_form t_atom l
    end.

  (* Preserve the array checker's input order while storing an exact canonical
     clause. Its default-true failure result is never an accepted certificate. *)
  Definition execute_array (m : machine) pos rule (c : C.t) : option machine :=
    let raw := array_clause rule in
    if fresh m pos &&
       forallb (fun l => Lit.blit l <? PArray.length t_form) (array_literals rule) &&
       clause_wf (PArray.length t_form) c &&
       clause_eqb (S.sort raw) c && negb (clause_eqb raw C._true) then
      Some (Machine (S.set_clause (clauses m) pos (S.sort raw)) (pos :: live m))
    else None.

  Definition execute (m : machine) (cmd : command) : option machine :=
    match cmd with
    | Command a c => execute_core m a c
    | BoolCongrCommand pos res eqs c => execute_bool m pos res eqs c
    | ArrayCommand pos rule c => execute_array m pos rule c
    end.

  Fixpoint run (m : machine) (cmds : list command) : option machine :=
    match cmds with
    | [] => Some m
    | cmd :: cmds =>
      match execute m cmd with
      | Some next => run next cmds
      | None => None
      end
    end.

  (* The trace passes this partially applied callback to every step. Keep the
     immutable table guard outside its changing premise/witness arguments. *)
  Definition prepared_gate (tables_ready : bool) : list C.t -> C.t -> witness -> bool :=
    fun cs c w => tables_ready &&
    clause_wf (PArray.length t_form) c &&
    match load_roots (PArray.length t_form) (initial (capacity w))
      (local_roots cs c) (root_claims w) with
    | None => false
    | Some m =>
      match run m (program w) with
      | None => false
      | Some m' => available m' (conflict w) &&
                   clause_eqb (S.get (clauses m') (conflict w)) []
      end
    end.

  Definition gate := prepared_gate (Form.check_form t_form && Atom.check_atom t_atom).

  (* Acceptance exposes exact roots, all local reads, a fresh bounded output,
     exact computed intermediate clauses, and explicit rejection of fallback. *)
  Lemma execute_core_binding : forall m a c m', execute_core m a c = Some m' ->
    exists p,
      decode a = Some p /\
      forallb (available m) (reads p) = true /\ fresh m (output p) = true /\
      m' = Machine (Euf_Checker.step_checker (clauses m) (semantic_step p))
                    (output p :: live m) /\
      S.get (clauses m') (output p) = c /\
      result_supported a (S.get (clauses m') (output p)) = true.
  Proof.
    intros m a c m' H; unfold execute_core in H.
    destruct (decode a) as [p| ] eqn:Hd; try discriminate.
    destruct (forallb (available m) (reads p) && fresh m (output p) &&
      forallb (fun l => Lit.blit l <? PArray.length t_form) (literals p))
      eqn:Hg; try discriminate.
    destruct (clause_wf (PArray.length t_form) (c) &&
      clause_eqb
        (S.get (Euf_Checker.step_checker (clauses m) (semantic_step p)) (output p))
        (c) &&
      result_supported a
        (S.get (Euf_Checker.step_checker (clauses m) (semantic_step p)) (output p))
        ) eqn:Hr; try discriminate.
    inversion H; subst; clear H; simpl.
    rewrite !andb_true_iff in Hg, Hr.
    destruct Hg as [[Hreads Hfresh] _]; destruct Hr as [[_ Heq] Hfallback].
    apply clause_eqb_spec in Heq.
    exists p; repeat split; assumption.
  Qed.

  Lemma execute_bool_binding : forall m pos res eqs c m',
    execute_bool m pos res eqs c = Some m' ->
    fresh m pos = true /\
    forallb (fun l => Lit.blit l <? PArray.length t_form)
      (res :: option_literals eqs) = true /\
    exists raw_clause, EunoiaBool.congr_clause t_i t_func t_atom t_form res eqs = Some raw_clause /\
      m' = Machine (S.set_clause (clauses m) pos raw_clause) (pos :: live m) /\
      clause_wf (PArray.length t_form) c = true /\
      S.get (clauses m') pos = c /\ c <> C._true.
  Proof.
    intros m pos res eqs c m' H; unfold execute_bool in H.
    destruct (fresh m pos && forallb
      (fun l => Lit.blit l <? PArray.length t_form)
      (res :: option_literals eqs)) eqn:Hg; try discriminate.
    destruct (EunoiaBool.congr_clause t_i t_func t_atom t_form res eqs)
      as [raw_clause| ] eqn:Hr; try discriminate.
    destruct (clause_wf (PArray.length t_form) c &&
      clause_eqb (S.get (S.set_clause (clauses m) pos raw_clause) pos) c &&
      negb (clause_eqb (S.get (S.set_clause (clauses m) pos raw_clause) pos) C._true))
      eqn:Hc; try discriminate.
    inversion H; subst; simpl.
    apply andb_true_iff in Hg as [Hfresh Hlit].
    apply andb_true_iff in Hc as [Hc Htrue].
    apply andb_true_iff in Hc as [Hwf Heq].
    apply clause_eqb_spec in Heq; rewrite Heq in Htrue.
    split; [exact Hfresh| ]; split; [exact Hlit| ].
    exists raw_clause; split; [reflexivity| ]; split; [reflexivity| ].
    split; [exact Hwf| ]; split; [exact Heq| ].
    intro E; rewrite E in Htrue.
    assert (clause_eqb C._true C._true = true) as Et.
    { apply clause_eqb_spec; reflexivity. }
    rewrite Et in Htrue; discriminate.
  Qed.

  Lemma array_clause_valid : forall rule,
    Form.check_form t_form = true -> Atom.check_atom t_atom = true ->
    Atom.wt t_i t_func t_atom -> C.valid valuation (array_clause rule).
  Proof.
    intros rule Hform Hatom Hwt; destruct rule; unfold array_clause, valuation.
    - eapply valid_check_roweq; eassumption.
    - eapply valid_check_rowneq; eassumption.
    - eapply valid_check_ext; eassumption.
  Qed.

  Lemma execute_array_binding : forall m pos rule c m',
    execute_array m pos rule c = Some m' ->
    fresh m pos = true /\
    forallb (fun l => Lit.blit l <? PArray.length t_form) (array_literals rule) = true /\
    clause_wf (PArray.length t_form) c = true /\
    S.sort (array_clause rule) = c /\ array_clause rule <> C._true /\
    m' = Machine (S.set_clause (clauses m) pos (S.sort (array_clause rule))) (pos :: live m).
  Proof.
    intros m pos rule c m' H; unfold execute_array in H.
    destruct (fresh m pos &&
      forallb (fun l => Lit.blit l <? PArray.length t_form) (array_literals rule) &&
      clause_wf (PArray.length t_form) c &&
      clause_eqb (S.sort (array_clause rule)) c &&
      negb (clause_eqb (array_clause rule) C._true)) eqn:Hg; try discriminate.
    inversion H; subst m'; clear H.
    rewrite !andb_true_iff in Hg.
    destruct Hg as [[[[Hfresh Hlit] Hwf] Heq] Hdefault].
    apply clause_eqb_spec in Heq.
    repeat split; try assumption.
    intro H; rewrite H in Hdefault.
    assert (clause_eqb C._true C._true = true) as Et by (apply clause_eqb_spec; reflexivity).
    rewrite Et in Hdefault; discriminate.
  Qed.

  Lemma execute_valid : forall m cmd m',
    Form.check_form t_form = true -> Atom.check_atom t_atom = true ->
    Atom.wt t_i t_func t_atom -> S.valid valuation (clauses m) ->
    execute m cmd = Some m' -> S.valid valuation (clauses m').
  Proof.
    intros m cmd m' Hform Hatom Hwt Hm H; destruct cmd as [a c|pos res eqs c|pos rule c].
    - destruct (@execute_core_binding m a c m' H)
        as [p [_ [_ [_ [-> _]]]]]; simpl.
      now apply Euf_Checker.step_checker_correct.
    - destruct (@execute_bool_binding m pos res eqs c m' H)
        as [_ [_ [raw_clause [Hr [-> _]]]]]; simpl.
      apply S.valid_set_clause; auto.
      + unfold valuation; apply (proj2 (Form.check_form_correct _ _ _ Hform)).
      + exact (EunoiaBool.congr_clause_sound t_i t_func t_atom t_form
          Hatom Hform res eqs raw_clause Hr).
    - destruct (@execute_array_binding m pos rule c m' H)
        as [_ [_ [_ [_ [_ ->]]]]]; simpl.
      assert (Hwf : Valuation.wf valuation).
      { unfold valuation; apply (proj2 (Form.check_form_correct _ _ _ Hform)). }
      apply S.valid_set_clause; auto.
      unfold C.valid; rewrite S.sort_correct by exact Hwf.
      eapply array_clause_valid; eassumption.
  Qed.

  Lemma run_valid : forall cmds m m',
    Form.check_form t_form = true -> Atom.check_atom t_atom = true ->
    Atom.wt t_i t_func t_atom -> S.valid valuation (clauses m) ->
    run m cmds = Some m' -> S.valid valuation (clauses m').
  Proof.
    induction cmds as [ |cmd cmds IH]; intros m m' Hform Hatom Hwt Hm H;
      simpl in H.
    - inversion H; subst; assumption.
    - destruct (execute m cmd) as [next| ] eqn:He; try discriminate.
      eapply (IH next m'); eauto; eapply execute_valid; eauto.
  Qed.

  (* Definitionally matches EunoiaChecker.gate_sound gate valuation, without
     depending on the coordinator's not-yet-integrated core module. *)
  Definition gate_sound (rho : Valuation.t) := forall cs c w,
    gate cs c w = true -> Forall (C.valid rho) cs -> C.valid rho c.

  Lemma gate_binding : forall cs c w, gate cs c w = true ->
    map snd (root_claims w) = local_roots cs c /\
    exists m m',
      load_roots (PArray.length t_form) (initial (capacity w))
        (local_roots cs c) (root_claims w) = Some m /\
      run m (program w) = Some m' /\
      available m' (conflict w) = true /\
      S.get (clauses m') (conflict w) = [].
  Proof.
    intros cs c w H; unfold gate, prepared_gate in H; rewrite !andb_true_iff in H.
    destruct H as [_ H].
    destruct (load_roots (PArray.length t_form) (initial (capacity w))
      (local_roots cs c) (root_claims w)) as [m| ] eqn:Hl; try discriminate.
    destruct (run m (program w)) as [m'| ] eqn:Hr; try discriminate.
    apply andb_true_iff in H; destruct H as [Ha Heq].
    apply clause_eqb_spec in Heq; split.
    - eapply load_roots_binding; eauto.
    - exists m, m'; repeat split; assumption.
  Qed.

  Theorem gate_correct : Atom.wt t_i t_func t_atom -> gate_sound valuation.
  Proof.
    intros Hwt cs c w Hgate Hcs; unfold gate, prepared_gate in Hgate.
    rewrite !andb_true_iff in Hgate.
    destruct Hgate as [[[Hform Hatom] Hc] Hgate].
    unfold C.valid; destruct (C.interp valuation c) eqn:Hfalse; [reflexivity| ].
    exfalso.
    destruct (load_roots (PArray.length t_form) (initial (capacity w))
      (local_roots cs c) (root_claims w)) as [m| ] eqn:Hl; try discriminate.
    destruct (run m (program w)) as [m'| ] eqn:Hr; try discriminate.
    apply andb_true_iff in Hgate; destruct Hgate as [_ Hconflict].
    apply clause_eqb_spec in Hconflict.
    assert (Valuation.wf valuation) as Hwf.
    { unfold valuation; apply (proj2 (Form.check_form_correct _ _ _ Hform)). }
    assert (S.valid valuation (clauses m)) as Hm.
    { eapply (@load_roots_valid valuation (PArray.length t_form)
        (local_roots cs c) (root_claims w) (initial (capacity w)) m Hwf).
      - now apply local_roots_valid.
      - apply S.valid_make; assumption.
      - exact Hl. }
    assert (S.valid valuation (clauses m')) as Hm'.
    { eapply (@run_valid (program w) m m'); eauto. }
    specialize (Hm' (conflict w)); rewrite Hconflict in Hm'; discriminate.
  Qed.
End Context.

Print Assumptions clause_eqb_spec.
Print Assumptions available_spec.
Print Assumptions fresh_spec.
Print Assumptions load_roots_binding.
Print Assumptions load_roots_valid.
Print Assumptions local_roots_valid.
Print Assumptions execute_core_binding.
Print Assumptions execute_bool_binding.
Print Assumptions execute_valid.
Print Assumptions run_valid.
Print Assumptions gate_binding.
Print Assumptions gate_correct.

End EunoiaLocal.
