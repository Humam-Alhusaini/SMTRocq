From SMTCoq Require Import SMTRocq.
From SMTCoq.structures Require Import BVList.
From Stdlib Require Import Bool NArith.
Import BITVECTOR_LIST.
Local Open Scope N_scope.

Lemma concat_low : forall x y : bitvector 8,
  @bv_extr 0 8 16 (bv_concat x y) = y.
Proof. Timeout 30 smtrocq. Qed.
Lemma concat_high : forall x y : bitvector 8,
  @bv_extr 8 8 16 (bv_concat x y) = x.
Proof. Timeout 30 smtrocq. Qed.
Lemma reconstruct_word : forall x : bitvector 16,
  bv_concat (@bv_extr 8 8 16 x) (@bv_extr 0 8 16 x) = x.
Proof. Timeout 30 smtrocq. Qed.
Lemma zero_extend_low : forall x : bitvector 8,
  @bv_extr 0 8 16 (@bv_zextn 8 8 x) = x.
Proof. Timeout 30 smtrocq. Qed.
Lemma zero_extend_high : forall x : bitvector 8,
  @bv_extr 8 8 16 (@bv_zextn 8 8 x) = zeros 8.
Proof. Timeout 30 smtrocq. Qed.
Lemma sign_extend_low : forall x : bitvector 8,
  @bv_extr 0 8 16 (@bv_sextn 8 8 x) = x.
Proof. Timeout 30 smtrocq. Qed.
Lemma zero_extend_identity : forall x : bitvector 8, @bv_zextn 8 0 x = x.
Proof. Timeout 30 smtrocq. Qed.
Lemma sign_extend_identity : forall x : bitvector 8, @bv_sextn 8 0 x = x.
Proof. Timeout 30 smtrocq. Qed.
Lemma sign_extend_composition : forall x : bitvector 8,
  @bv_sextn 16 4 (@bv_sextn 8 8 x) = @bv_sextn 8 12 x.
Proof. Timeout 30 smtrocq. Qed.
Lemma extract_bitwise : forall x y : bitvector 8,
  @bv_extr 2 4 8 (bv_and x y) = bv_and (@bv_extr 2 4 8 x) (@bv_extr 2 4 8 y).
Proof. Timeout 30 smtrocq. Qed.
Lemma concat_negation : forall x y : bitvector 8,
  bv_not (bv_concat x y) = bv_concat (bv_not x) (bv_not y).
Proof. Timeout 30 smtrocq. Qed.
Lemma sign_extend_negation : forall x : bitvector 8,
  bv_not (@bv_sextn 8 8 x) = @bv_sextn 8 8 (bv_not x).
Proof. Timeout 30 smtrocq. Qed.

Example reject_concat_commutation : True.
Proof. Fail assert (forall x y : bitvector 8, bv_concat x y = bv_concat y x) by smtrocq. exact I. Qed.
Example reject_wrong_half : True.
Proof. Fail assert (forall x y : bitvector 8, @bv_extr 0 8 16 (bv_concat x y) = x) by smtrocq. exact I. Qed.
Example reject_sign_as_zero_extension : True.
Proof. Fail assert (forall x : bitvector 8, @bv_sextn 8 8 x = @bv_zextn 8 8 x) by smtrocq. exact I. Qed.
Example reject_zero_extension_negation : True.
Proof. Fail assert (forall x : bitvector 8, bv_not (@bv_zextn 8 8 x) = @bv_zextn 8 8 (bv_not x)) by smtrocq. exact I. Qed.
(* Rocq defines out-of-range extraction, but it is outside this SMT-LIB path. *)
Example unsupported_extraction_range : True.
Proof. Fail assert (forall x : bitvector 8, @bv_extr 8 8 8 x = zeros 8) by smtrocq. exact I. Qed.

Lemma reconstruct_32 : forall x : bitvector 32,
  bv_concat (@bv_extr 16 16 32 x) (@bv_extr 0 16 32 x) = x.
Proof. Timeout 30 smtrocq. Qed.
Lemma extract_negation : forall x : bitvector 8,
  @bv_extr 2 4 8 (bv_not x) = bv_not (@bv_extr 2 4 8 x).
Proof. Timeout 30 smtrocq. Qed.

Lemma reconstruct_64 : forall x : bitvector 64,
  bv_concat (@bv_extr 32 32 64 x) (@bv_extr 0 32 64 x) = x.
Proof. Timeout 30 smtrocq. Qed.
