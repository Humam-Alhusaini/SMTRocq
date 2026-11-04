(* SMTCoq -- distributed under the CeCILL-C licence (see LICENSE). *)
From Stdlib Require Import List String Bool.
From SMTCoq.checker.eunoia Require Import EoSyntax EoRuntime CpcGenerated.
From SMTCoq.checker.eunoia Require Import EoNameIndex EoIndexed.
Import ListNotations.
Open Scope string_scope.
Definition program_index : EoNameIndex.trie program := Eval vm_compute in EoNameIndex.from_list cpc_programs.
Definition program_lookup name := EoNameIndex.lookup name program_index.
Theorem program_lookup_correct : forall name, program_lookup name=named name cpc_programs.
Proof.
 intro; unfold program_lookup.
 change (EoNameIndex.lookup name (EoNameIndex.from_list cpc_programs)=named name cpc_programs).
 apply EoNameIndex.lookup_from_list.
Qed.
Definition derive_context_with_index (extra : primitive_hook) (fuel : nat) (typeof : term -> option term)
    (name : string) (assumption : option term) (args premises : list term) : option term :=
  let canon := rename_symbols cpc_aliases in
  let surface := rename_symbols cpc_surface_names in
  let all_inputs := ((match assumption with Some a => [a] | None => [] end) ++ args ++ premises)%list in
  if forallb (surface_supported_with_arities cpc_unary_operators cpc_blocked_operators cpc_binary_operators) (map canon all_inputs) then
  let query := (fun t => option_map canon (typeof (surface t))) in
  let nilof := resolve_nil extra cpc_operators fuel query cpc_programs cpc_nils in
  option_map surface (EoIndexed.run_surface cpc_polymorphic_operators nilof extra fuel
    (fun t => option_map canon (typeof (surface t)))
    cpc_operators cpc_programs program_lookup cpc_rules name (option_map canon assumption) (map canon args) (map canon premises)) else None.


Theorem derive_context_with_index_refinement : forall extra fuel typeof name assumption args premises,
 derive_context_with_index extra fuel typeof name assumption args premises=
 CpcGenerated.derive_context_with extra fuel typeof name assumption args premises.
Proof.
 intros. unfold derive_context_with_index,CpcGenerated.derive_context_with.
 destruct (forallb _ _); [|reflexivity].
 rewrite EoIndexed.run_surface_refinement; [reflexivity|apply program_lookup_correct].
Qed.
Definition derive_indexed fuel typeof name args premises :=
 derive_context_with_index default_primitive fuel typeof name None args premises.
Theorem derive_indexed_refinement : forall fuel typeof name args premises,
 derive_indexed fuel typeof name args premises=derive fuel typeof name args premises.
Proof. intros; apply derive_context_with_index_refinement. Qed.
Print Assumptions derive_indexed_refinement.

Definition derive_assuming_indexed fuel typeof name assumption args premises :=
 derive_context_with_index default_primitive fuel typeof name (Some assumption) args premises.
Theorem derive_assuming_indexed_refinement : forall fuel typeof name assumption args premises,
 derive_assuming_indexed fuel typeof name assumption args premises=derive_assuming fuel typeof name assumption args premises.
Proof. intros; apply derive_context_with_index_refinement. Qed.
