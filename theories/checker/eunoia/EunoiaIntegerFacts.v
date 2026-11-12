(* Proved facts about actual Rocq integer functions, not additional SMT axioms. *)
From Stdlib Require Import Bool ZArith Lia.
Local Open Scope Z_scope.
Module EunoiaIntegerFacts.
Lemma abs_laws : forall x,
 ((0 <=? Z.abs x) &&
  (implb (0 <=? x) (Z.abs x =? x) &&
   implb (x <=? 0) (Z.abs x =? -x)))%bool = true.
Proof.
 intros x; repeat rewrite andb_true_iff.
 rewrite !implb_true_iff, !Z.leb_le, !Z.eqb_eq.
 repeat split; intros; [apply Z.abs_nonneg|apply Z.abs_eq|apply Z.abs_neq]; lia.
Qed.
Lemma min_laws : forall x y,
 ((Z.min x y <=? x) && ((Z.min x y <=? y) &&
  (implb (x <=? y) (Z.min x y =? x) &&
   implb (y <=? x) (Z.min x y =? y))))%bool = true.
Proof.
 intros x y; repeat rewrite andb_true_iff.
 rewrite !implb_true_iff, !Z.leb_le, !Z.eqb_eq.
 repeat split; intros; [apply Z.le_min_l|apply Z.le_min_r|apply Z.min_l|apply Z.min_r]; assumption.
Qed.
Lemma max_laws : forall x y,
 ((x <=? Z.max x y) && ((y <=? Z.max x y) &&
  (implb (y <=? x) (Z.max x y =? x) &&
   implb (x <=? y) (Z.max x y =? y))))%bool = true.
Proof.
 intros x y; repeat rewrite andb_true_iff.
 rewrite !implb_true_iff, !Z.leb_le, !Z.eqb_eq.
 repeat split; intros; [apply Z.le_max_l|apply Z.le_max_r|apply Z.max_l|apply Z.max_r]; assumption.
Qed.
Lemma sign_laws : forall x,
 (implb (x <? 0) (Z.sgn x =? -1) &&
 (implb (x =? 0) (Z.sgn x =? 0) &&
  implb (0 <? x) (Z.sgn x =? 1)))%bool = true.
Proof.
 intros x; repeat rewrite andb_true_iff.
 rewrite !implb_true_iff, !Z.ltb_lt, !Z.eqb_eq.
 destruct x; cbn; intros; repeat split; intros; try reflexivity; lia.
Qed.
Lemma symbolic_positive_modulo : forall x d,
 implb (0 <? d) ((0 <=? x mod d) && (x mod d <? d)) = true.
Proof.
 intros; rewrite implb_true_iff, Z.ltb_lt, andb_true_iff, Z.leb_le, Z.ltb_lt.
 apply Z.mod_pos_bound.
Qed.
Lemma symbolic_negative_modulo : forall x d,
 implb (d <? 0) ((d <? x mod d) && (x mod d <=? 0)) = true.
Proof.
 intros; rewrite implb_true_iff, Z.ltb_lt, andb_true_iff, Z.ltb_lt, Z.leb_le.
 apply Z.mod_neg_bound.
Qed.
Lemma symbolic_zero_division : forall x d,
 implb (d =? 0) (((x/d =? 0) && (x mod d =? x))) = true.
Proof.
 intros; rewrite implb_true_iff, Z.eqb_eq; intro; subst d.
 rewrite Z.div_0_r, Z.mod_0_r, !Z.eqb_refl; reflexivity.
Qed.
Lemma known_quotient_divisor : forall x d n,
 (d =? n) = true -> (x/d =? x/n) = true.
Proof. intros x d n H; apply Z.eqb_eq in H; subst d; apply Z.eqb_refl. Qed.
Lemma known_remainder_divisor : forall x d n,
 (d =? n) = true -> (x mod d =? x mod n) = true.
Proof. intros x d n H; apply Z.eqb_eq in H; subst d; apply Z.eqb_refl. Qed.
End EunoiaIntegerFacts.
