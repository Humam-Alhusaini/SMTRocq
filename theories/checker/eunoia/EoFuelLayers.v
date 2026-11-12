(* SMTCoq -- distributed under the CeCILL-C licence (see LICENSE). *)
(* Lazy, structurally terminating helper layers. *)
From Stdlib Require Import List String Arith Lia.
From SMTCoq.checker.eunoia Require Import EoSyntax EoRuntime.
Import ListNotations.
Open Scope string_scope.
Module EoFuelLayers.
Definition evaluator := string -> list term -> computation term.
Definition handler := nat -> evaluator.
Inductive layer := Layer : evaluator -> (unit -> option layer) -> layer.
Definition run (l:layer) := match l with Layer f _=>f end.
Definition tail (l:layer) := match l with Layer _ next=>next tt end.
Fixpoint fetch depth (l:layer) : option layer :=
 match depth with 0=>Some l|S d=>match tail l with Some l'=>fetch d l'|None=>None end end.
Section Builder.
 Variable build:nat->handler->evaluator.
 Fixpoint make fuel : layer :=
 match fuel with
 | 0=>Layer (build 0 (fun _ _ _=>Missing "fuel exhausted")) (fun _=>None)
 | S k=>Layer
   (build (S k) (fun depth name args=>match depth with
     | 0=>Missing "invalid staged helper depth"
     | S d=>match fetch d (make k) with Some l=>run l name args|None=>Missing "fuel exhausted" end
     end))
   (fun _=>Some(make k))
 end.
 Lemma fetch_make : forall depth fuel,
 fetch depth (make fuel)=if Nat.leb depth fuel then Some(make(fuel-depth)) else None.
 Proof.
  induction depth as [|d IH]; intros fuel; [simpl;now rewrite Nat.sub_0_r|].
  destruct fuel as [|fuel]; [reflexivity|].
  cbn [make fetch tail]. apply IH.
 Qed.
 Variable reference:nat->evaluator.
 Hypothesis build_correct : forall fuel calls,
  (forall depth name args,0<depth<=fuel -> calls depth name args=reference(fuel-depth)name args) ->
  forall name args,build fuel calls name args=reference fuel name args.
 Theorem make_correct : forall fuel name args,run(make fuel)name args=reference fuel name args.
 Proof.
  intro fuel; induction fuel using lt_wf_ind; intros name args.
  destruct fuel as [|fuel].
  - cbn [make run]. apply build_correct. intros;lia.
  - cbn [make run]. apply build_correct. intros depth name' args' Hd.
    destruct depth as [|depth]; [lia|].
    rewrite fetch_make.
    assert (Hle:Nat.leb depth fuel=true) by (apply Nat.leb_le;lia).
    rewrite Hle. apply H. lia.
 Qed.
End Builder.
Print Assumptions make_correct.
End EoFuelLayers.
