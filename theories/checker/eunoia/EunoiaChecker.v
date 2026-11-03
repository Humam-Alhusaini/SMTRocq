(**************************************************************************)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2026                                          *)
(*     Distributed under the terms of the CeCILL-C licence (see LICENSE). *)
(**************************************************************************)

From Stdlib Require Import List Bool Uint63.
From SMTCoq.utils Require Import PArray.
From SMTCoq.checker.fol Require Import State Terms.

Import ListNotations.
Local Open Scope uint63_scope.
Local Open Scope array_scope.
Set Implicit Arguments.

Module EunoiaChecker.

(* Exact equality: no weakening, permutation or normalization at this gate. *)
Fixpoint clause_eqb (a b : C.t) : bool :=
  match a, b with
  | [], [] => true
  | x :: xs, y :: ys => (x =? y) && clause_eqb xs ys
  | _, _ => false
  end.

Lemma clause_eqb_spec : forall a b, clause_eqb a b = true <-> a = b.
Proof.
  induction a as [|x xs IH]; destruct b as [|y ys]; simpl;
    try (split; [discriminate | congruence]).
  - tauto.
  - rewrite andb_true_iff, Uint63.eqb_spec, IH.
    split; [intros [-> ->]; reflexivity | intro H; inversion H; auto].
Qed.

Definition clause_wf (nforms : int) (c : C.t) : bool :=
  forallb (fun l => Lit.blit l <? nforms) c && clause_eqb (S.sort c) c.

Record machine := Machine {
  clauses : S.t;
  live : list clause_id
}.

Definition initial (capacity : int) := Machine (S.make capacity) [].

(* This includes freshness and bounds, in addition to the existing S invariant. *)
Definition invariant (rho : Valuation.t) (m : machine) : Prop :=
  S.valid rho (clauses m) /\ NoDup (live m) /\
  forall id, In id (live m) -> (id <? PArray.length (clauses m)) = true.

Definition available (m : machine) (id : clause_id) : bool :=
  (id <? PArray.length (clauses m)) && existsb (fun j => id =? j) (live m).

Fixpoint fetch (m : machine) (ids : list clause_id) : option (list C.t) :=
  match ids with
  | [] => Some []
  | id :: ids =>
    if available m id then
      match fetch m ids with
      | Some cs => Some (S.get (clauses m) id :: cs)
      | None => None
      end
    else None
  end.

Definition store (nforms : int) (m : machine) (id : clause_id) (c : C.t)
  : option machine :=
  if (id <? PArray.length (clauses m)) &&
     negb (existsb (fun j => id =? j) (live m)) && clause_wf nforms c
  then Some (Machine (S.set_clause (clauses m) id c) (id :: live m))
  else None.

Lemma initial_invariant : forall rho capacity,
  Valuation.wf rho -> invariant rho (initial capacity).
Proof.
  intros rho capacity Hwf; split; simpl.
  - now apply S.valid_make.
  - split; [constructor | intros id H; contradiction].
Qed.

Lemma available_spec : forall m id, available m id = true <->
  (id <? PArray.length (clauses m)) = true /\ In id (live m).
Proof.
  intros m id; unfold available; rewrite andb_true_iff, existsb_exists.
  split.
  - intros [Hb [j [Hj Heq]]]; apply Uint63.eqb_spec in Heq; subst; auto.
  - intros [Hb Hi]; split; auto; exists id; split; auto.
    apply Uint63.eqb_refl.
Qed.

Lemma fetch_valid : forall rho m ids cs,
  S.valid rho (clauses m) -> fetch m ids = Some cs ->
  Forall (C.valid rho) cs.
Proof.
  intros rho m ids; induction ids as [|id ids IH]; intros cs Hv H;
    simpl in H.
  - inversion H; constructor.
  - destruct (available m id); try discriminate.
    destruct (fetch m ids) as [tail|] eqn:Ht; try discriminate.
    inversion H; subst; constructor; [apply Hv | eapply IH]; eauto.
Qed.

(* Successful reads expose the exact ordered clauses, and cannot use defaults. *)
Lemma fetch_exact : forall m ids cs,
  fetch m ids = Some cs ->
  cs = map (S.get (clauses m)) ids /\ Forall (fun id => available m id = true) ids.
Proof.
  intros m ids; induction ids as [|id ids IH]; intros cs H; simpl in H.
  - inversion H; split; [reflexivity | constructor].
  - destruct (available m id) eqn:Ha; try discriminate.
    destruct (fetch m ids) as [tail|] eqn:Ht; try discriminate.
    inversion H; subst cs; destruct (IH _ eq_refl) as [-> Hids].
    split; [reflexivity | constructor; assumption].
Qed.

Lemma store_invariant : forall rho nforms m id c m',
  Valuation.wf rho -> invariant rho m -> C.valid rho c ->
  store nforms m id c = Some m' -> invariant rho m'.
Proof.
  intros rho nforms m id c m' Hwf [Hv [Hnd Hb]] Hc H.
  unfold store in H.
  destruct ((id <? PArray.length (clauses m)) &&
    negb (existsb (fun j => id =? j) (live m)) && clause_wf nforms c)
    eqn:Hg; try discriminate.
  inversion H; subst m'; clear H.
  apply andb_true_iff in Hg; destruct Hg as [Hg _].
  apply andb_true_iff in Hg; destruct Hg as [Hid Hfresh].
  split; simpl; [now apply S.valid_set_clause | split].
  - constructor; auto.
    intro Hin; apply negb_true_iff in Hfresh.
    assert (existsb (fun j => id =? j) (live m) = true) as Hex.
    { apply existsb_exists; exists id; split; auto; apply Uint63.eqb_refl. }
    congruence.
  - intros j [<-|Hin]; unfold S.set_clause; rewrite PArray.length_set; auto.
Qed.

Lemma store_exact : forall nforms m id c m',
  store nforms m id c = Some m' ->
  S.get (clauses m') id = c /\ live m' = id :: live m.
Proof.
  intros nforms m id c m' H; unfold store in H.
  destruct ((id <? PArray.length (clauses m)) &&
    negb (existsb (fun j => id =? j) (live m)) && clause_wf nforms c)
    eqn:Hg; try discriminate.
  inversion H; subst; simpl.
  rewrite !andb_true_iff in Hg; destruct Hg as [[Hb _] Hc].
  unfold clause_wf in Hc; apply andb_true_iff in Hc.
  destruct Hc as [_ Hc]; apply clause_eqb_spec in Hc.
  split; auto; unfold S.get, S.set_clause.
  now rewrite PArray.get_set_same, Hc.
Qed.

(* The executable interface has no rule syntax or rule-name cases. *)
Section Generic.
  Context {rule witness : Type}.
  Variable eval : rule -> list C.t -> option C.t.
  Variable gate : list C.t -> C.t -> witness -> bool.

  Record step := Step {
    destination : clause_id;
    premises : list clause_id;
    payload : rule;
    conclusion : C.t;
    evidence : witness
  }.

  Definition check_step (nforms : int) (m : machine) (st : step)
    : option machine :=
    match fetch m (premises st) with
    | None => None
    | Some cs =>
      match eval (payload st) cs with
      | None => None
      | Some c =>
        if clause_eqb c (conclusion st) && gate cs (conclusion st) (evidence st)
        then store nforms m (destination st) (conclusion st)
        else None
      end
    end.

  Fixpoint run (nforms : int) (m : machine) (trace : list step)
    : option machine :=
    match trace with
    | [] => Some m
    | st :: rest =>
      match check_step nforms m st with
      | Some m' => run nforms m' rest
      | None => None
      end
    end.

  (* A proposition about a concrete gate, never a global semantic assumption. *)
  Definition gate_sound (rho : Valuation.t) : Prop :=
    forall cs c w, gate cs c w = true -> Forall (C.valid rho) cs -> C.valid rho c.

  Lemma check_step_binding : forall nforms m st m',
    check_step nforms m st = Some m' ->
    exists cs,
      fetch m (premises st) = Some cs /\
      eval (payload st) cs = Some (conclusion st) /\
      gate cs (conclusion st) (evidence st) = true /\
      S.get (clauses m') (destination st) = conclusion st /\
      live m' = destination st :: live m.
  Proof.
    intros nforms m st m' H; unfold check_step in H.
    destruct (fetch m (premises st)) as [cs|] eqn:Hf; try discriminate.
    destruct (eval (payload st) cs) as [c|] eqn:He; try discriminate.
    destruct (clause_eqb c (conclusion st) && gate cs (conclusion st) (evidence st))
      eqn:Hg; try discriminate.
    apply andb_true_iff in Hg; destruct Hg as [Hc Hg].
    apply clause_eqb_spec in Hc; subst c.
    destruct (@store_exact nforms m (destination st) (conclusion st) m' H)
      as [Hs Hl]; exists cs; auto.
  Qed.

  Lemma check_step_invariant : forall rho nforms m st m',
    Valuation.wf rho -> gate_sound rho -> invariant rho m ->
    check_step nforms m st = Some m' -> invariant rho m'.
  Proof.
    intros rho nforms m st m' Hwf Hgate Hinv H.
    unfold check_step in H.
    destruct (fetch m (premises st)) as [cs|] eqn:Hf; try discriminate.
    destruct (eval (payload st) cs) as [c|]; try discriminate.
    destruct (clause_eqb c (conclusion st) && gate cs (conclusion st) (evidence st))
      eqn:Hg; try discriminate.
    apply andb_true_iff in Hg; destruct Hg as [_ Hg].
    eapply store_invariant; eauto.
    eapply Hgate; eauto; eapply fetch_valid; eauto; apply Hinv.
  Qed.

  Lemma run_invariant : forall rho nforms trace m m',
    Valuation.wf rho -> gate_sound rho -> invariant rho m ->
    run nforms m trace = Some m' -> invariant rho m'.
  Proof.
    intros rho nforms trace; induction trace as [|st trace IH];
      intros m m' Hwf Hgate Hinv H; simpl in H.
    - inversion H; subst; assumption.
    - destruct (check_step nforms m st) as [next|] eqn:Hs; try discriminate.
      apply (IH next m' Hwf Hgate); [|exact H].
      eapply check_step_invariant; eauto.
  Qed.
End Generic.

(* Root claims cannot add, omit, reorder, or alter the caller's root clauses. *)
Fixpoint load_roots (nforms : int) (m : machine)
  (roots : list C.t) (claims : list (clause_id * C.t)) : option machine :=
  match roots, claims with
  | [], [] => Some m
  | c :: roots, (id, claimed) :: claims =>
    if clause_eqb c claimed then
      match store nforms m id claimed with
      | Some m' => load_roots nforms m' roots claims
      | None => None
      end
    else None
  | _, _ => None
  end.

Lemma load_roots_invariant : forall rho nforms roots claims m m',
  Valuation.wf rho -> Forall (C.valid rho) roots -> invariant rho m ->
  load_roots nforms m roots claims = Some m' -> invariant rho m'.
Proof.
  intros rho nforms roots; induction roots as [|c roots IH];
    intros claims m m' Hwf Hr Hinv H; destruct claims as [|[id claimed] claims];
    simpl in H; try discriminate.
  - inversion H; subst; assumption.
  - destruct (clause_eqb c claimed) eqn:Hc; try discriminate.
    apply clause_eqb_spec in Hc; subst claimed.
    destruct (store nforms m id c) as [next|] eqn:Hs; try discriminate.
    inversion Hr; subst; apply (IH claims next m' Hwf); auto.
    eapply store_invariant; eauto.
Qed.

Definition conflict (m : machine) (goal : clause_id) : bool :=
  available m goal && C.is_false (S.get (clauses m) goal).

Definition checker {rule witness : Type}
  (eval : rule -> list C.t -> option C.t)
  (gate : list C.t -> C.t -> witness -> bool)
  (nforms capacity : int) (roots : list C.t)
  (claims : list (clause_id * C.t)) (trace : list (@step rule witness))
  (goal : clause_id) : bool :=
  match load_roots nforms (initial capacity) roots claims with
  | None => false
  | Some m =>
    match run eval gate nforms m trace with
    | None => false
    | Some m' => conflict m' goal
    end
  end.

Theorem checker_correct : forall (rule witness : Type) eval gate
  nforms capacity roots claims (trace : list (@step rule witness)) goal rho,
  Valuation.wf rho -> gate_sound gate rho ->
  checker eval gate nforms capacity roots claims trace goal = true ->
  ~ Forall (C.valid rho) roots.
Proof.
  intros rule witness eval gate nforms capacity roots claims trace goal rho
    Hwf Hgate H Hr.
  unfold checker in H.
  destruct (load_roots nforms (initial capacity) roots claims) as [m|] eqn:Hl;
    try discriminate.
  destruct (run eval gate nforms m trace) as [m'|] eqn:Ht; try discriminate.
  assert (invariant rho m) as Hm.
  { eapply load_roots_invariant; eauto; now apply initial_invariant. }
  assert (invariant rho m') as Hm'.
  { eapply run_invariant; eauto. }
  unfold conflict in H; apply andb_true_iff in H; destruct H as [_ Hfalse].
  apply (C.is_false_correct _ Hfalse rho).
  destruct Hm' as [Hv _]; apply Hv.
Qed.

Print Assumptions fetch_valid.
Print Assumptions store_invariant.
Print Assumptions check_step_invariant.
Print Assumptions run_invariant.
Print Assumptions load_roots_invariant.
Print Assumptions checker_correct.

End EunoiaChecker.
