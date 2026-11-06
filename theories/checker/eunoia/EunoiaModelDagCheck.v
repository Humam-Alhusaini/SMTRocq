(* SMTCoq -- distributed under the CeCILL-C licence (see LICENSE). *)
From Stdlib Require Import List Bool Uint63.
From SMTCoq.utils Require Import PArray CompDec.
From SMTCoq.checker.fol Require Import State Terms.
From SMTCoq.checker.eunoia Require Import CpcGenerated EunoiaAdapter EunoiaScope EunoiaScopedAdapter
 EunoiaMemo EunoiaModelDag EunoiaTactic.
Import ListNotations.
Local Open Scope uint63_scope.
Local Open Scope array_scope.
Module EunoiaModelDagCheck.
(* Full source-and-semantic checker. Only construction of the exact model
   encodings changes; generated rule evaluation and all gates stay the same. *)
Definition trace:=EunoiaMemo.trace.
Definition discharge:=EunoiaMemo.discharge.
Section Tables.
Variable t_i:array typ_compdec.
Variable t_func:array(Atom.tval t_i).
Variable t_atom:array Atom.atom.
Variable t_form:array Form.form.
Variable names:EunoiaAdapter.naming.
Definition checker fuel entries capacity roots root_terms claims(t:trace)goal:=
 let ready:=EunoiaAdapter.tables_wf t_i t_func t_atom t_form names in
 let names_ready:=EunoiaAdapter.names_wf t_i t_func names in
 let encodings:=EunoiaModelDag.encoding_entries t_i t_func t_atom t_form names fuel
  (List.concat roots++EunoiaScope.literals t)%list in
 ready&&EunoiaAdapter.bind_terms t_i t_func t_atom t_form names fuel roots root_terms&&
 @EunoiaMemo.cache_valid t_i t_func t_atom t_form entries&&
 EunoiaScope.checker
  (EunoiaAdapter.prepared_eval_with t_i t_func t_atom t_form names encodings ready names_ready CpcGenerated.derive fuel)
  (@EunoiaScopedAdapter.prepared_scope_eval_with t_i t_func t_atom t_form names encodings ready names_ready CpcGenerated.default_primitive fuel)
  (@EunoiaMemo.gate t_i t_func t_atom t_form entries)(PArray.length t_form)capacity roots claims t goal.
Theorem checker_refinement:forall fuel entries capacity roots root_terms claims t goal,
 checker fuel entries capacity roots root_terms claims t goal=
 @EunoiaMemo.checker t_i t_func t_atom t_form names fuel entries capacity roots root_terms claims t goal.
Proof. intros;unfold checker,EunoiaMemo.checker,EunoiaMemo.checker_with;rewrite EunoiaModelDag.encoding_entries_refinement;reflexivity. Qed.
Definition valuation:=@EunoiaMemo.valuation t_i t_func t_atom t_form.
Theorem checker_correct:forall fuel entries capacity roots root_terms claims t goal,
 checker fuel entries capacity roots root_terms claims t goal=true->~Forall(C.valid valuation)roots.
Proof. intros;rewrite checker_refinement in H;eapply EunoiaMemo.checker_correct;exact H. Qed.
Definition checker_b fuel entries capacity l b root_terms claims t goal:=
 checker fuel entries capacity(EunoiaTactic.goal_roots l b)root_terms claims t goal.
Theorem checker_b_refinement:forall fuel entries capacity l b root_terms claims t goal,
 checker_b fuel entries capacity l b root_terms claims t goal=
 @EunoiaMemo.checker_b t_i t_func t_atom t_form names fuel entries capacity l b root_terms claims t goal.
Proof. intros;apply checker_refinement. Qed.
Theorem checker_b_correct:forall fuel entries capacity l b root_terms claims t goal,
 checker_b fuel entries capacity l b root_terms claims t goal=true->Lit.interp valuation l=b.
Proof. intros;rewrite checker_b_refinement in H;eapply EunoiaMemo.checker_b_correct;exact H. Qed.
Definition checker_eq fuel entries capacity l1 l2 l root_terms claims t goal:=
 if Lit.is_pos l then false else match t_form.[Lit.blit l]with
 |Form.Fiff a b=>(l1 =? a)&&(l2 =? b)&&checker_b fuel entries capacity(Lit.neg l)true root_terms claims t goal
 |_=>false end.
Theorem checker_eq_refinement:forall fuel entries capacity l1 l2 l root_terms claims t goal,
 checker_eq fuel entries capacity l1 l2 l root_terms claims t goal=
 @EunoiaMemo.checker_eq t_i t_func t_atom t_form names fuel entries capacity l1 l2 l root_terms claims t goal.
Proof.
 intros;unfold checker_eq,EunoiaMemo.checker_eq,EunoiaMemo.checker_eq_with.
 destruct(Lit.is_pos l);[reflexivity|].
 destruct(t_form.[Lit.blit l]);try reflexivity;rewrite checker_b_refinement;reflexivity.
Qed.
Theorem checker_eq_correct:forall fuel entries capacity l1 l2 l root_terms claims t goal,
 checker_eq fuel entries capacity l1 l2 l root_terms claims t goal=true->Lit.interp valuation l1=Lit.interp valuation l2.
Proof. intros;rewrite checker_eq_refinement in H;eapply EunoiaMemo.checker_eq_correct;exact H. Qed.
End Tables.
Print Assumptions checker_refinement.
Print Assumptions checker_correct.
End EunoiaModelDagCheck.
