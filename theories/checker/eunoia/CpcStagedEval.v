(* SMTCoq -- distributed under the CeCILL-C licence (see LICENSE). *)
From Stdlib Require Import List String Arith Lia.
From SMTCoq.checker.eunoia Require Import EoSyntax EoRuntime CpcGenerated EoCheckedMemo.
From SMTCoq.checker.eunoia Require Import EoStaged EoFuelLayers CpcStaged.
Import ListNotations EoCheckedMemo.
Open Scope string_scope.
Module CpcStagedEval.
Section Context.
 Variable nilof:nil_query.
 Variable extra:primitive_hook.
 Variable typeof:term->option term.
 Definition evaluate fuel table env e :=
 let layer:=EoFuelLayers.make (CpcStaged.build_with nilof typeof table) fuel in
 let calls:=fun depth name args=>match EoFuelLayers.fetch depth layer with
   |Some l=>EoFuelLayers.run l name args|None=>Missing "fuel exhausted" end in
 EoStaged.compile nilof extra cpc_operators typeof cpc_programs e 0 calls fuel env.
 Theorem evaluate_correct : forall fuel env e,
 evaluate fuel (CpcStaged.code_table nilof extra typeof) env e=
 evaluate_computation nilof extra cpc_operators fuel typeof cpc_programs env e.
 Proof.
 intros;unfold evaluate.
 apply(EoStaged.compile_refinement nilof extra cpc_operators typeof cpc_programs fuel);[|lia].
 intros depth name args Hd. rewrite EoFuelLayers.fetch_make.
 assert(Hle:Nat.leb depth fuel=true)by(apply Nat.leb_le;lia).
 rewrite Hle.
 change(CpcStaged.execute nilof extra typeof (fuel-depth) name args=call_reference nilof extra cpc_operators (fuel-depth) typeof cpc_programs name args).
 apply CpcStaged.execute_correct.
 Qed.
End Context.
End CpcStagedEval.
