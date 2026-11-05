(* SMTCoq -- distributed under the CeCILL-C licence (see LICENSE). *)
From Stdlib Require Import List String Bool.
From SMTCoq.checker.eunoia Require Import EoSyntax EoRuntime EoRuleMemo CpcGenerated.
Import ListNotations.
Open Scope string_scope.
Module EoSpecialized.

(* Preparing one statically selected rule avoids constructing the complete
   rule inventory. These otherwise unused arguments disappear by reduction. *)
Definition prepare_one {A:Type} (continue:rule->bindings->option A)
    polymorphic nilof typeof ops r assumption args premises :=
 EoRuleMemo.with_prepared_rule continue polymorphic nilof no_extension ops
   0 typeof [] [("",r)] "" assumption args premises.
Lemma prepare_one_correct : forall A (continue:rule->bindings->option A)
    polymorphic nilof extra ops fuel typeof programs rules name r assumption args premises,
 named name rules=Some r ->
 EoRuleMemo.with_prepared_rule continue polymorphic nilof extra ops fuel typeof programs
   rules name assumption args premises =
 prepare_one continue polymorphic nilof typeof ops r assumption args premises.
Proof. intros;unfold prepare_one,EoRuleMemo.with_prepared_rule;rewrite H;reflexivity. Qed.
Lemma prepare_one_ext : forall A (f g:rule->bindings->option A)
    polymorphic nilof typeof ops r assumption args premises,
 (forall env,f r env=g r env) ->
 prepare_one f polymorphic nilof typeof ops r assumption args premises =
 prepare_one g polymorphic nilof typeof ops r assumption args premises.
Proof.
 intros;unfold prepare_one,EoRuleMemo.with_prepared_rule;cbn [named String.eqb].
 repeat first[reflexivity|apply H|progress cbn beta iota zeta|
 match goal with |-context[match ?x with _=>_ end]=>destruct x eqn:? end].
Qed.

Record implementation := Implementation {
 key : string;
 execute : nil_query -> primitive_hook -> nat -> (term->option term) ->
           option term -> list term -> list term -> option term;
 execute_correct : forall nilof extra fuel typeof assumption args premises,
   execute nilof extra fuel typeof assumption args premises =
   run_rule_assuming_with_nils_polymorphic cpc_polymorphic_operators nilof extra
     cpc_operators fuel typeof cpc_programs cpc_rules key assumption args premises
}.
Fixpoint find name (implementations:list implementation) :=
 match implementations with
 |[]=>None
 |i::rest=>if String.eqb name (key i) then Some i else find name rest
 end.
Lemma find_key:forall implementations name i,
 find name implementations=Some i -> key i=name.
Proof.
 induction implementations as[|j rest IH];intros name i H;[discriminate|].
 cbn [find] in H;destruct(String.eqb name (key j)) eqn:E.
 - inversion H;subst;apply String.eqb_eq in E;symmetry;exact E.
 - now apply IH in H.
Qed.
Definition run_using implementations nilof extra fuel typeof name assumption args premises :=
 match find name implementations with
 |Some i=>execute i nilof extra fuel typeof assumption args premises
 |None=>run_rule_assuming_with_nils_polymorphic cpc_polymorphic_operators nilof extra
     cpc_operators fuel typeof cpc_programs cpc_rules name assumption args premises
 end.
Theorem run_using_correct : forall implementations nilof extra fuel typeof name assumption args premises,
 run_using implementations nilof extra fuel typeof name assumption args premises =
 run_rule_assuming_with_nils_polymorphic cpc_polymorphic_operators nilof extra
   cpc_operators fuel typeof cpc_programs cpc_rules name assumption args premises.
Proof.
 intros;unfold run_using;destruct(find name implementations) as[i|] eqn:H;[|reflexivity].
 rewrite execute_correct,(find_key _ _ _ H);reflexivity.
Qed.
Definition run_surface implementations nilof extra fuel typeof name assumption args premises :=
 EoRuleMemo.surface_using (fun q=>run_using implementations nilof extra fuel q)
 cpc_polymorphic_operators nilof extra fuel typeof cpc_operators cpc_programs cpc_rules
 name assumption args premises.
Lemma run_surface_correct : forall implementations nilof extra fuel typeof name assumption args premises,
 run_surface implementations nilof extra fuel typeof name assumption args premises=
 run_surface_rule_assuming_with_nils_polymorphic cpc_polymorphic_operators nilof extra fuel typeof
 cpc_operators cpc_programs cpc_rules name assumption args premises.
Proof.
 intros;unfold run_surface,EoRuleMemo.surface_using,run_surface_rule_assuming_with_nils_polymorphic.
 fold(EoRuleMemo.internal_query nilof typeof fuel cpc_operators).
 repeat first[reflexivity|rewrite run_using_correct|
 match goal with |-context[match ?x with _=>_ end]=>destruct x eqn:? end].
Qed.
Definition derive_context implementations (extra:primitive_hook)(fuel:nat)(typeof:term->option term)
    (name:string)(assumption:option term)(args premises:list term):option term :=
 let canon:=cpc_canonicalize in
 let surface:=cpc_surface in
 let all_inputs:=((match assumption with Some a=>[a]|None=>[] end)++args++premises)%list in
 if forallb (surface_supported_with_arities cpc_unary_operators cpc_blocked_operators cpc_binary_operators)
     (map canon all_inputs) then
 let query:=fun t=>option_map canon (typeof(surface t)) in
 let nilof:=resolve_nil extra cpc_operators fuel query cpc_programs cpc_nils in
 option_map surface (run_surface implementations nilof extra fuel query name
   (option_map canon assumption)(map canon args)(map canon premises)) else None.
Theorem derive_context_correct : forall implementations extra fuel typeof name assumption args premises,
 derive_context implementations extra fuel typeof name assumption args premises=
 derive_context_with extra fuel typeof name assumption args premises.
Proof.
 intros;unfold derive_context,derive_context_with.
 destruct(forallb _ _);[|reflexivity]. rewrite run_surface_correct;reflexivity.
Qed.
Print Assumptions prepare_one_correct.
Print Assumptions run_using_correct.
Print Assumptions derive_context_correct.
End EoSpecialized.
