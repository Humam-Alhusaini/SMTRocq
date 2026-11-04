(* SMTCoq -- distributed under the CeCILL-C licence (see LICENSE). *)
From Stdlib Require Import List String.
From SMTCoq.checker.eunoia Require Import EoSyntax EoRuntime CpcGenerated EoCheckedMemo.
From SMTCoq.checker.eunoia Require Import CpcDirect.
Import ListNotations EoCheckedMemo.
Open Scope string_scope.
Module CpcDirectEntry.
Definition implementation := nat->list term->computation term.
Fixpoint choose fuel name args (table:list(string*implementation)) :=
 match table with
 |[]=>Missing("program "++name)
 |(key,run)::rest=>if String.eqb name key then run fuel args else choose fuel name args rest
 end.
Lemma choose_correct:forall table fuel name args,
 choose fuel name args table=
 match named name table with None=>Missing("program "++name)|Some run=>run fuel args end.
Proof.
 induction table as[|[key run]rest IH];intros;[reflexivity|].
 cbn [choose named];destruct(String.eqb name key);[reflexivity|apply IH].
Qed.
Definition dispatch := Eval cbv [choose CpcDirect.compiled] in
 fun nilof extra typeof fuel name args=>choose fuel name args(CpcDirect.compiled nilof extra typeof).
Theorem dispatch_correct:forall nilof extra typeof fuel name args,
 dispatch nilof extra typeof fuel name args=
 call_reference nilof extra cpc_operators fuel typeof cpc_programs name args.
Proof.
 intros;change(choose fuel name args(CpcDirect.compiled nilof extra typeof)=call_reference nilof extra cpc_operators fuel typeof cpc_programs name args).
 rewrite choose_correct.
 change(CpcDirect.dispatch nilof extra typeof fuel name args=call_reference nilof extra cpc_operators fuel typeof cpc_programs name args).
 apply CpcDirect.dispatch_correct.
Qed.
Print Assumptions dispatch_correct.
End CpcDirectEntry.
