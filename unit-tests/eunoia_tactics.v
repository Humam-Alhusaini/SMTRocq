(**************************************************************************)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2026                                          *)
(*     Distributed under the terms of the CeCILL-C licence (see LICENSE). *)
(**************************************************************************)

From SMTCoq Require Import SMTRocq.
From Stdlib Require Import ZArith.
Local Open Scope Z_scope.

(* A live cvc5 invocation, followed by generated CPC computation and checking. *)
Lemma eunoia_live_reflexivity (x : Z) : x = x.
Proof. cvc5_eunoia. Qed.
Print Assumptions eunoia_live_reflexivity.

Lemma eunoia_live_congruence (f : Z -> Z) (x y : Z) :
  x = y -> f x = f y.
Proof. cvc5_eunoia. Qed.
Print Assumptions eunoia_live_congruence.

(* The carrier universe belongs to the goal's evar map, not a Section. *)
Lemma eunoia_quantified_carrier :
  forall (A : Type) (HA : CompDec A) (f : A -> A) (x y : A),
    x = y -> f x = f y.
Proof. cvc5_eunoia. Qed.
Print Assumptions eunoia_quantified_carrier.

Example eunoia_rejects_false_goal : True.
Proof.
  Fail assert ((0 : Z) = 1) by cvc5_eunoia.
  exact I.
Qed.

Example eunoia_rejects_arbitrary_equality : True.
Proof.
  Fail assert (forall x y : Z, x = y) by cvc5_eunoia.
  exact I.
Qed.

(* Proof-producing Boolean translation of compound hypotheses. *)
Lemma eunoia_frontend_implications (a b c : bool) :
  (a = true -> b = true) -> (b = true -> c = true) -> a = true -> c = true.
Proof. cvc5_eunoia. Qed.

Lemma eunoia_frontend_iff_negation (a b : bool) :
  (a = true <-> b = true) -> (a = false <-> b = false).
Proof. cvc5_eunoia. Qed.

(* Legacy preprocessing supplies inferred comparison instances for carriers
   absent from the local context; the direct path deliberately falls back. *)
Lemma eunoia_frontend_instance_fallback (f : list Z -> list Z) (x y : list Z) :
  x = y -> f x = f y.
Proof. cvc5_eunoia. Qed.

Example eunoia_frontend_fallback_rejects_false : True.
Proof.
  Fail assert (forall (f : list Z -> list Z) (x y : list Z),
    f x = f y -> x = y) by cvc5_eunoia.
  exact I.
Qed.

(* Explicit facts retain their original preprocessing and proof context. *)
Lemma eunoia_frontend_supplied_fact (x : Z) : x = x.
Proof. cvc5_eunoia (eunoia_live_reflexivity x). Qed.
