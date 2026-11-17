From SMTCoq Require Import SMTRocq.
From SMTCoq.structures Require Import FArray.
From Stdlib Require Import Bool ZArith.
Local Open Scope Z_scope.

Lemma array_absolute_index : forall (a : FArray.farray Z Z) (i v : Z),
  FArray.select (FArray.store a (Z.abs i) v) (-1) = FArray.select a (-1).
Proof. Timeout 30 smtrocq. Qed.

Lemma array_maximum_value : forall (a : FArray.farray Z Z) (i x y : Z),
  x <= FArray.select (FArray.store a i (Z.max x y)) i.
Proof. Timeout 30 smtrocq. Qed.

Lemma array_minimum_alias : forall (a : FArray.farray Z Z) (i j v : Z),
  i <= j -> FArray.select (FArray.store a (Z.min i j) v) i = v.
Proof. Timeout 30 smtrocq. Qed.

Lemma array_remainder_value : forall (a : FArray.farray Z Z) (i x d : Z),
  0 < d -> 0 <= FArray.select (FArray.store a i (x mod d)) i < d.
Proof. Timeout 30 smtrocq. Qed.

Example reject_array_absolute_alias : True.
Proof.
  Fail assert (forall (a : FArray.farray Z Z) (i v : Z),
    FArray.select (FArray.store a (Z.abs i) v) 0 = FArray.select a 0) by smtrocq.
  exact I.
Qed.
