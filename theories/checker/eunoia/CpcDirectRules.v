(* SMTCoq -- distributed under the CeCILL-C licence (see LICENSE). *)
From Stdlib Require Import List String Arith.
From SMTCoq.checker.eunoia Require Import EoSyntax EoRuntime CpcGenerated EoRuleMemo CpcMemo.
From SMTCoq.checker.eunoia Require Import CpcDirectEval.
Import ListNotations.
Open Scope string_scope.
Module CpcDirectRules.
Definition run_rule nilof extra fuel typeof name assumption args premises :=
 EoRuleMemo.with_prepared_rule
 (EoRuleMemo.execute_using
   (fun env e=>computed(CpcDirectEval.evaluate nilof extra typeof fuel env e)) typeof)
 cpc_polymorphic_operators nilof extra cpc_operators fuel typeof cpc_programs cpc_rules name assumption args premises.
Lemma run_rule_correct : forall nilof extra fuel typeof name assumption args premises,
 run_rule nilof extra fuel typeof name assumption args premises=
 run_rule_assuming_with_nils_polymorphic cpc_polymorphic_operators nilof extra cpc_operators fuel typeof cpc_programs cpc_rules name assumption args premises.
Proof.
 intros;rewrite EoRuleMemo.reference_factorization;unfold run_rule.
 apply EoRuleMemo.with_prepared_rule_ext;intros r env;apply EoRuleMemo.execute_using_ext;intros env' e.
 rewrite CpcDirectEval.evaluate_correct;reflexivity.
Qed.
Definition run_surface nilof extra fuel typeof name assumption args premises :=
 EoRuleMemo.surface_using (fun q=>run_rule nilof extra fuel q)
 cpc_polymorphic_operators nilof extra fuel typeof cpc_operators cpc_programs cpc_rules name assumption args premises.
Lemma run_surface_correct : forall nilof extra fuel typeof name assumption args premises,
 run_surface nilof extra fuel typeof
 name assumption args premises=
 run_surface_rule_assuming_with_nils_polymorphic cpc_polymorphic_operators nilof extra fuel typeof cpc_operators cpc_programs cpc_rules name assumption args premises.
Proof.
 intros;unfold run_surface,EoRuleMemo.surface_using,run_surface_rule_assuming_with_nils_polymorphic.
 fold(EoRuleMemo.internal_query nilof typeof fuel cpc_operators).
 repeat first[reflexivity|rewrite run_rule_correct|
 match goal with |-context[match ?x with _=>_ end]=>destruct x eqn:? end].
Qed.
Definition derive_context (extra : primitive_hook) (fuel : nat) (typeof : term -> option term)
    (name : string) (assumption : option term) (args premises : list term) : option term :=
  let canon := cpc_canonicalize in
  let surface := cpc_surface in
  let all_inputs := ((match assumption with Some a => [a] | None => [] end) ++ args ++ premises)%list in
  if forallb (surface_supported_with_arities cpc_unary_operators cpc_blocked_operators cpc_binary_operators) (map canon all_inputs) then
  let query := (fun t => option_map canon (typeof (surface t))) in
  let nilof := resolve_nil extra cpc_operators fuel query cpc_programs cpc_nils in
  option_map surface (run_surface nilof extra fuel
    (fun t => option_map canon (typeof (surface t)))
    name (option_map canon assumption) (map canon args) (map canon premises)) else None.


Theorem derive_context_correct : forall extra fuel typeof name assumption args premises,
 derive_context extra fuel typeof name assumption args premises=
 derive_context_with extra fuel typeof name assumption args premises.
Proof.
 intros;unfold derive_context,derive_context_with.
 destruct(forallb _ _);[|reflexivity].
 rewrite run_surface_correct;reflexivity.
Qed.
Print Assumptions derive_context_correct.
End CpcDirectRules.
