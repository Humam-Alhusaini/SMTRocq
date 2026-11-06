(* SMTCoq -- distributed under the CeCILL-C licence (see LICENSE). *)
From Stdlib Require Import List Bool String Uint63.
From SMTCoq.utils Require Import PArray CompDec.
From SMTCoq.checker.fol Require Import State Terms.
From SMTCoq.checker.eunoia Require Import EoSyntax EoRuntime CpcGenerated EunoiaChecker
 EunoiaAdapter EunoiaLocal EunoiaScope EunoiaTactic EunoiaScopedAdapter EunoiaHelperCache.
From SMTCoq.checker.eunoia Require Import CpcDirectRules.
Import ListNotations.
Local Open Scope uint63_scope.
Local Open Scope array_scope.
Set Implicit Arguments.
Module EunoiaDirectScoped.
Section Tables.
 Variable t_i:array typ_compdec.
 Variable t_func:array (Atom.tval t_i).
 Variable t_atom:array Atom.atom.
 Variable t_form:array Form.form.
 Variable names:EunoiaAdapter.naming.
 Local Abbreviation ready := (EunoiaAdapter.tables_wf t_i t_func t_atom t_form names).
 Local Abbreviation names_ready := (EunoiaAdapter.names_wf t_i t_func names).
 Local Abbreviation query fuel := (EunoiaAdapter.typeof_with_ready t_i t_func names names_ready fuel).
 Definition checker fuel capacity roots root_terms claims (t:EunoiaScopedAdapter.trace) goal :=
 let encodings:=EunoiaAdapter.encoding_entries t_i t_func t_atom t_form names fuel
   (List.concat roots ++ EunoiaScope.literals t)%list in
 ready && EunoiaAdapter.bind_terms t_i t_func t_atom t_form names fuel roots root_terms &&
 EunoiaScope.checker
   (EunoiaAdapter.prepared_eval_with t_i t_func t_atom t_form names encodings ready names_ready
     (fun _ _ name args premises=>CpcDirectRules.derive_context CpcGenerated.default_primitive fuel (query fuel) name None args premises) fuel)
   (@EunoiaScopedAdapter.prepared_scope_eval_with t_i t_func t_atom t_form names encodings ready names_ready CpcGenerated.default_primitive fuel)
   (@EunoiaLocal.gate t_i t_func t_atom t_form) (PArray.length t_form)
   capacity roots claims t goal.
 Lemma checker_refinement : forall fuel capacity roots root_terms claims t goal,
 checker fuel capacity roots root_terms claims t goal=true ->
 @EunoiaScopedAdapter.checker t_i t_func t_atom t_form names fuel capacity roots root_terms claims t goal=true.
 Proof.
 intros fuel capacity roots root_terms claims t goal H.
 unfold checker in H.
 unfold EunoiaScopedAdapter.checker, EunoiaScopedAdapter.checker_with.
 erewrite <- EunoiaHelperCache.checker_ext; [exact H|].
 intros p cs; unfold EunoiaAdapter.prepared_eval_with.
 destruct (EunoiaAdapter.source_assumption p); [reflexivity|].
 destruct (ready && EunoiaAdapter.cached_bind_terms _ _ _ _ _ _ _ _ _); [|reflexivity].
 rewrite CpcDirectRules.derive_context_correct. reflexivity.
 Qed.
 Definition valuation := @EunoiaScopedAdapter.valuation t_i t_func t_atom t_form.
 Theorem checker_correct : forall fuel capacity roots root_terms claims t goal,
 checker fuel capacity roots root_terms claims t goal=true -> ~Forall (C.valid valuation) roots.
 Proof. intros; eapply EunoiaScopedAdapter.checker_correct; eapply checker_refinement; exact H. Qed.
 Definition checker_b fuel capacity l b root_terms claims t goal :=
 checker fuel capacity (EunoiaTactic.goal_roots l b) root_terms claims t goal.
 Lemma checker_b_refinement : forall fuel capacity l b root_terms claims t goal,
 checker_b fuel capacity l b root_terms claims t goal=true ->
 @EunoiaScopedAdapter.checker_b t_i t_func t_atom t_form names fuel capacity l b root_terms claims t goal=true.
 Proof. intros; eapply checker_refinement; exact H. Qed.
 Theorem checker_b_correct : forall fuel capacity l b root_terms claims t goal,
 checker_b fuel capacity l b root_terms claims t goal=true -> Lit.interp valuation l=b.
 Proof. intros; eapply EunoiaScopedAdapter.checker_b_correct; eapply checker_b_refinement; exact H. Qed.
 Definition checker_eq fuel capacity l1 l2 l root_terms claims t goal :=
 if Lit.is_pos l then false else match t_form.[Lit.blit l] with
 | Form.Fiff a b=>(l1 =? a)&&(l2 =? b)&&checker_b fuel capacity (Lit.neg l) true root_terms claims t goal
 | _=>false end.
 Lemma checker_eq_refinement : forall fuel capacity l1 l2 l root_terms claims t goal,
 checker_eq fuel capacity l1 l2 l root_terms claims t goal=true ->
 @EunoiaScopedAdapter.checker_eq t_i t_func t_atom t_form names fuel capacity l1 l2 l root_terms claims t goal=true.
 Proof.
 intros; unfold checker_eq in H; unfold EunoiaScopedAdapter.checker_eq, EunoiaScopedAdapter.checker_eq_with.
 destruct (Lit.is_pos l); [discriminate|]. destruct (t_form.[Lit.blit l]); try discriminate.
 apply andb_true_iff in H; destruct H as [He Hrun]. apply andb_true_iff; split; [exact He|].
 eapply checker_b_refinement; exact Hrun.
 Qed.
 Theorem checker_eq_correct : forall fuel capacity l1 l2 l root_terms claims t goal,
 checker_eq fuel capacity l1 l2 l root_terms claims t goal=true -> Lit.interp valuation l1=Lit.interp valuation l2.
 Proof. intros; eapply EunoiaScopedAdapter.checker_eq_correct; eapply checker_eq_refinement; exact H. Qed.
End Tables.
End EunoiaDirectScoped.
Print Assumptions EunoiaDirectScoped.checker_refinement.
Print Assumptions EunoiaDirectScoped.checker_correct.
Print Assumptions EunoiaDirectScoped.checker_b_correct.
Print Assumptions EunoiaDirectScoped.checker_eq_correct.
