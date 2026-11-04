(* SMTCoq -- distributed under the CeCILL-C licence (see LICENSE). *)
From Stdlib Require Import List Bool String Uint63.
From SMTCoq.utils Require Import PArray CompDec.
From SMTCoq.checker.fol Require Import State Terms.
From SMTCoq.checker.eunoia Require Import EoSyntax EoRuntime CpcGenerated EunoiaChecker
 EunoiaAdapter EunoiaLocal EunoiaScope EunoiaTactic EunoiaScopedAdapter EunoiaMemo.
From SMTCoq.checker.eunoia Require Import EoCheckedMemo CpcMemo.
Import ListNotations.
Local Open Scope uint63_scope.
Local Open Scope array_scope.
Set Implicit Arguments.
Module EunoiaHelperCache.
Section Extensionality.
 Context {rule scope_rule witness:Type}.
 Variables (f g:rule->list C.t->option C.t)
   (scope:scope_rule->_lit->C.t->option C.t)
   (gate:list C.t->C.t->witness->bool).
 Hypothesis Heq:forall r cs,f r cs=g r cs.
 Lemma step_ext : forall n m st,
 EunoiaChecker.check_step f gate n m st=EunoiaChecker.check_step g gate n m st.
 Proof. intros; unfold EunoiaChecker.check_step; destruct (EunoiaChecker.fetch _ _); [now rewrite Heq|reflexivity]. Qed.
 Lemma run_ext : forall (t:@EunoiaScope.trace rule scope_rule witness) n m,
 EunoiaScope.run f scope gate n m t=EunoiaScope.run g scope gate n m t.
 Proof.
 induction t as [|st rest IH|slot a body IHbody closing rest IHrest]; intros n m; simpl; [reflexivity| |].
 - rewrite step_ext. destruct (EunoiaChecker.check_step g gate n m st); [apply IH|reflexivity].
 - destruct closing; [|reflexivity]. destruct (EunoiaChecker.store n m slot [a]); [|reflexivity].
   rewrite IHbody. destruct (EunoiaScope.run g scope gate n m0 body); [|reflexivity].
   destruct (EunoiaScope.close scope gate n m m1 a d); [apply IHrest|reflexivity].
 Qed.
 Lemma checker_ext : forall n capacity roots claims t goal,
 EunoiaScope.checker f scope gate n capacity roots claims t goal=
 EunoiaScope.checker g scope gate n capacity roots claims t goal.
 Proof. intros; unfold EunoiaScope.checker; destruct (EunoiaChecker.load_roots _ _ _ _); [now rewrite run_ext|reflexivity]. Qed.
End Extensionality.
Section Tables.
 Variable t_i:array typ_compdec.
 Variable t_func:array (Atom.tval t_i).
 Variable t_atom:array Atom.atom.
 Variable t_form:array Form.form.
 Variable names:EunoiaAdapter.naming.
 Local Abbreviation ready := (EunoiaAdapter.tables_wf t_i t_func t_atom t_form names).
 Local Abbreviation names_ready := (EunoiaAdapter.names_wf t_i t_func names).
 Local Abbreviation query fuel := (EunoiaAdapter.typeof_with_ready t_i t_func names names_ready fuel).
 Definition checker fuel helpers entries capacity roots root_terms claims (t:EunoiaMemo.trace) goal :=
 match validate_context CpcGenerated.default_primitive fuel (query fuel) helpers with
 | None=>false
 | Some cache=>
 let encodings:=EunoiaAdapter.encoding_entries t_i t_func t_atom t_form names fuel
   (List.concat roots ++ EunoiaScope.literals t)%list in
 ready && EunoiaAdapter.bind_terms t_i t_func t_atom t_form names fuel roots root_terms &&
 @EunoiaMemo.cache_valid t_i t_func t_atom t_form entries &&
 EunoiaScope.checker
   (EunoiaAdapter.prepared_eval_with t_i t_func t_atom t_form names encodings ready names_ready
     (fun fuel typeof name args premises=>derive_context_cached cache CpcGenerated.default_primitive fuel typeof name None args premises) fuel)
   (@EunoiaScopedAdapter.prepared_scope_eval_with t_i t_func t_atom t_form names encodings ready names_ready CpcGenerated.default_primitive fuel)
   (@EunoiaMemo.gate t_i t_func t_atom t_form entries) (PArray.length t_form)
   capacity roots claims t goal
 end.
 Lemma checker_refinement : forall fuel helpers entries capacity roots root_terms claims t goal,
 checker fuel helpers entries capacity roots root_terms claims t goal=true ->
 @EunoiaMemo.checker t_i t_func t_atom t_form names fuel entries capacity roots root_terms claims t goal=true.
 Proof.
 intros fuel helpers entries capacity roots root_terms claims t goal H.
 unfold checker in H.
 destruct (validate_context CpcGenerated.default_primitive fuel (query fuel) helpers) as [cache|] eqn:Hcache; [|discriminate].
 pose proof (validate_context_sound _ _ _ _ _ Hcache) as Hv.
 unfold EunoiaMemo.checker, EunoiaMemo.checker_with.
 erewrite <- checker_ext; [exact H|].
 intros p cs; unfold EunoiaAdapter.prepared_eval_with.
 destruct (EunoiaAdapter.source_assumption p); [reflexivity|].
 destruct (ready && EunoiaAdapter.cached_bind_terms _ _ _ _ _ _ _ _ _); [|reflexivity].
 rewrite derive_context_cached_refinement by exact Hv. reflexivity.
 Qed.
 Definition valuation := @EunoiaMemo.valuation t_i t_func t_atom t_form.
 Theorem checker_correct : forall fuel helpers entries capacity roots root_terms claims t goal,
 checker fuel helpers entries capacity roots root_terms claims t goal=true -> ~Forall (C.valid valuation) roots.
 Proof. intros; eapply EunoiaMemo.checker_correct; eapply checker_refinement; exact H. Qed.
 Definition checker_b fuel helpers entries capacity l b root_terms claims t goal :=
 checker fuel helpers entries capacity (EunoiaTactic.goal_roots l b) root_terms claims t goal.
 Lemma checker_b_refinement : forall fuel helpers entries capacity l b root_terms claims t goal,
 checker_b fuel helpers entries capacity l b root_terms claims t goal=true ->
 @EunoiaMemo.checker_b t_i t_func t_atom t_form names fuel entries capacity l b root_terms claims t goal=true.
 Proof. intros; eapply checker_refinement; exact H. Qed.
 Theorem checker_b_correct : forall fuel helpers entries capacity l b root_terms claims t goal,
 checker_b fuel helpers entries capacity l b root_terms claims t goal=true -> Lit.interp valuation l=b.
 Proof. intros; eapply EunoiaMemo.checker_b_correct; eapply checker_b_refinement; exact H. Qed.
 Definition checker_eq fuel helpers entries capacity l1 l2 l root_terms claims t goal :=
 if Lit.is_pos l then false else match t_form.[Lit.blit l] with
 | Form.Fiff a b=>(l1 =? a)&&(l2 =? b)&&checker_b fuel helpers entries capacity (Lit.neg l) true root_terms claims t goal
 | _=>false end.
 Lemma checker_eq_refinement : forall fuel helpers entries capacity l1 l2 l root_terms claims t goal,
 checker_eq fuel helpers entries capacity l1 l2 l root_terms claims t goal=true ->
 @EunoiaMemo.checker_eq t_i t_func t_atom t_form names fuel entries capacity l1 l2 l root_terms claims t goal=true.
 Proof.
 intros; unfold checker_eq in H; unfold EunoiaMemo.checker_eq, EunoiaMemo.checker_eq_with.
 destruct (Lit.is_pos l); [discriminate|]. destruct (t_form.[Lit.blit l]); try discriminate.
 apply andb_true_iff in H; destruct H as [He Hrun]. apply andb_true_iff; split; [exact He|].
 eapply checker_b_refinement; exact Hrun.
 Qed.
 Theorem checker_eq_correct : forall fuel helpers entries capacity l1 l2 l root_terms claims t goal,
 checker_eq fuel helpers entries capacity l1 l2 l root_terms claims t goal=true -> Lit.interp valuation l1=Lit.interp valuation l2.
 Proof. intros; eapply EunoiaMemo.checker_eq_correct; eapply checker_eq_refinement; exact H. Qed.
End Tables.
End EunoiaHelperCache.
Print Assumptions EunoiaHelperCache.checker_refinement.
Print Assumptions EunoiaHelperCache.checker_correct.
Print Assumptions EunoiaHelperCache.checker_b_correct.
Print Assumptions EunoiaHelperCache.checker_eq_correct.
