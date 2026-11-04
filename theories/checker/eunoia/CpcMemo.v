(* SMTCoq -- distributed under the CeCILL-C licence (see LICENSE). *)
From Stdlib Require Import List String Bool Arith.
From SMTCoq.checker.eunoia Require Import EoSyntax EoRuntime CpcGenerated.
From SMTCoq.checker.eunoia Require Import EoCheckedMemo EoRuleMemo.
Import ListNotations EoCheckedMemo.EoCheckedMemo.
Local Open Scope string_scope.
Definition surface_query typeof t := option_map (rename_symbols cpc_aliases) (typeof (rename_symbols cpc_surface_names t)).
Definition context_nilof extra fuel typeof := resolve_nil extra cpc_operators fuel (surface_query typeof) cpc_programs cpc_nils.
Definition context_query extra fuel typeof := EoRuleMemo.internal_query
 (context_nilof extra fuel typeof) (surface_query typeof) fuel cpc_operators.
Definition context_valid extra fuel typeof cache := cache_valid (context_nilof extra fuel typeof)
 extra cpc_operators fuel (context_query extra fuel typeof) cpc_programs cache.
Definition validate_context extra fuel typeof entries := validate_entries (context_nilof extra fuel typeof)
 extra cpc_operators fuel (context_query extra fuel typeof) cpc_programs entries.
Theorem validate_context_sound : forall extra fuel typeof entries cache,
 validate_context extra fuel typeof entries=Some cache -> context_valid extra fuel typeof cache.
Proof. intros; eapply validate_entries_sound; exact H. Qed.
Definition derive_context_cached (cache:list cache_entry) (extra : primitive_hook) (fuel : nat) (typeof : term -> option term)
    (name : string) (assumption : option term) (args premises : list term) : option term :=
  let canon := rename_symbols cpc_aliases in
  let surface := rename_symbols cpc_surface_names in
  let all_inputs := ((match assumption with Some a => [a] | None => [] end) ++ args ++ premises)%list in
  if forallb (surface_supported_with_arities cpc_unary_operators cpc_blocked_operators cpc_binary_operators) (map canon all_inputs) then
  let query := (fun t => option_map canon (typeof (surface t))) in
  let nilof := resolve_nil extra cpc_operators fuel query cpc_programs cpc_nils in
  option_map surface (EoRuleMemo.run_surface_cached cpc_polymorphic_operators nilof extra fuel
    (fun t => option_map canon (typeof (surface t)))
    cpc_operators cpc_programs cache cpc_rules name (option_map canon assumption) (map canon args) (map canon premises)) else None.


Theorem derive_context_cached_refinement : forall cache extra fuel typeof name assumption args premises,
 context_valid extra fuel typeof cache ->
 derive_context_cached cache extra fuel typeof name assumption args premises =
 CpcGenerated.derive_context_with extra fuel typeof name assumption args premises.
Proof.
 intros. unfold derive_context_cached, CpcGenerated.derive_context_with.
 destruct (forallb _ _); [|reflexivity].
 rewrite EoRuleMemo.run_surface_cached_refinement; [reflexivity|exact H].
Qed.
Definition derive_checked entries extra fuel typeof name assumption args premises :=
 match validate_context extra fuel typeof entries with
 | Some cache=>derive_context_cached cache extra fuel typeof name assumption args premises
 | None=>None end.
Theorem derive_checked_correct : forall entries extra fuel typeof name assumption args premises value,
 derive_checked entries extra fuel typeof name assumption args premises=Some value ->
 CpcGenerated.derive_context_with extra fuel typeof name assumption args premises=Some value.
Proof.
 intros. unfold derive_checked in H.
 destruct (validate_context extra fuel typeof entries) as [cache|] eqn:Hcache; [|discriminate].
 rewrite derive_context_cached_refinement in H; [exact H|eapply validate_context_sound; exact Hcache].
Qed.
Print Assumptions derive_checked_correct.
