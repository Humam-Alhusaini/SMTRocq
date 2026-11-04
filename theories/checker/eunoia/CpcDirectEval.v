(* SMTCoq -- distributed under the CeCILL-C licence (see LICENSE). *)
From Stdlib Require Import List String Arith Lia.
From SMTCoq.checker.eunoia Require Import EoSyntax EoRuntime CpcGenerated.
From SMTCoq.checker.eunoia Require Import EoDirect CpcDirectEntry.
Module CpcDirectEval.
Definition evaluate nilof extra typeof fuel env e :=
 EoDirect.compile nilof extra cpc_operators typeof cpc_programs e
   (CpcDirectEntry.dispatch nilof extra typeof) fuel env.
Theorem evaluate_correct:forall nilof extra typeof fuel env e,
 evaluate nilof extra typeof fuel env e=
 evaluate_computation nilof extra cpc_operators fuel typeof cpc_programs env e.
Proof.
 intros;unfold evaluate;apply EoDirect.compile_refinement.
 intros;apply CpcDirectEntry.dispatch_correct.
Qed.
Print Assumptions evaluate_correct.
End CpcDirectEval.
