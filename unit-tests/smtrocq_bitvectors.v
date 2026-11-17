From SMTCoq Require Import SMTRocq.
From SMTCoq.structures Require Import BVList.
From Stdlib Require Import Bool NArith List.
Import ListNotations.
Import BITVECTOR_LIST.

Lemma bv_and_commute : forall x y : bitvector 8%N,
  bv_and x y = bv_and y x.
Proof. Timeout 30 smtrocq. Qed.

Lemma bv_or_commute : forall x y : bitvector 8%N,
  bv_or x y = bv_or y x.
Proof. Timeout 30 smtrocq. Qed.

Lemma bv_not_involution : forall x : bitvector 8%N,
  bv_not (bv_not x) = x.
Proof. Timeout 30 smtrocq. Qed.

Lemma bv_xor_self : forall x : bitvector 8%N,
  bv_xor x x = zeros 8%N.
Proof. Timeout 30 smtrocq. Qed.

Lemma bv_bitwise_congruence : forall x y z : bitvector 8%N,
  x = y -> bv_and x (bv_not z) = bv_and y (bv_not z).
Proof. Timeout 30 smtrocq. Qed.

Lemma bv_demorgan : forall x y : bitvector 8%N,
  bv_not (bv_and x y) = bv_or (bv_not x) (bv_not y).
Proof. Timeout 30 smtrocq. Qed.

Example bv_reject_wrong_and : True.
Proof.
  Fail assert (forall x y : bitvector 8%N, bv_and x y = x) by smtrocq.
  exact I.
Qed.

Example bv_reject_wrong_not : True.
Proof.
  Fail assert (forall x : bitvector 8%N, bv_not x = x) by smtrocq.
  exact I.
Qed.

Lemma bv_constant_order :
  bv_not (of_bits [true;false;true;false;true;false;true;false]) =
  of_bits [false;true;false;true;false;true;false;true].
Proof. Timeout 30 smtrocq. Qed.

Example bv_reject_arbitrary_zero : True.
Proof.
  Fail assert (forall x : bitvector 8%N, x = zeros 8%N) by smtrocq.
  exact I.
Qed.
