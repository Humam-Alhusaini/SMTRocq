(**************************************************************************)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2026                                          *)
(*     Distributed under the terms of the CeCILL-C licence (see LICENSE). *)
(**************************************************************************)

From SMTCoq Require Import SMTCoq.
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
