From Stdlib Require Import Bool ZArith Lia.
Local Open Scope Z_scope.
Module EunoiaDivision.
Lemma positive_laws : forall x (p : positive),
  ((x =? Zpos p * (x / Zpos p) + x mod Zpos p) &&
   ((0 <=? x mod Zpos p) && (x mod Zpos p <? Zpos p)))%bool = true.
Proof.
  intros x p. repeat rewrite andb_true_iff.
  rewrite Z.eqb_eq, Z.leb_le, Z.ltb_lt.
  split; [apply Z.div_mod; lia | apply Z.mod_pos_bound; lia].
Qed.
Lemma negative_laws : forall x (p : positive),
  ((x =? Zneg p * (x / Zneg p) + x mod Zneg p) &&
   ((Zneg p <? x mod Zneg p) && (x mod Zneg p <=? 0)))%bool = true.
Proof.
  intros x p. repeat rewrite andb_true_iff.
  rewrite Z.eqb_eq, Z.ltb_lt, Z.leb_le.
  split; [apply Z.div_mod; lia | apply Z.mod_neg_bound; lia].
Qed.
Lemma zero_laws : forall x,
  (((x / 0) =? 0) && ((x mod 0) =? x))%bool = true.
Proof. intros x; rewrite Z.div_0_r, Z.mod_0_r, !Z.eqb_refl; reflexivity. Qed.
Lemma shift_laws : forall x k d, d <> 0 ->
  (((x+k*d)/d =? x/d+k) && ((x+k*d) mod d =? x mod d))%bool = true.
Proof. intros; rewrite andb_true_iff, !Z.eqb_eq. split; [apply Z.div_add | apply Z.mod_add]; assumption. Qed.
Lemma positive_shift_laws : forall x k (p:positive),
  (((x+k*Zpos p)/Zpos p =? x/Zpos p+k) &&
   ((x+k*Zpos p) mod Zpos p =? x mod Zpos p))%bool = true.
Proof. intros; apply shift_laws; lia. Qed.
Lemma negative_shift_laws : forall x k (p:positive),
  (((x+k*Zneg p)/Zneg p =? x/Zneg p+k) &&
   ((x+k*Zneg p) mod Zneg p =? x mod Zneg p))%bool = true.
Proof. intros; apply shift_laws; lia. Qed.
Lemma nested_positive_law : forall x d (p:positive), d <> 0 ->
  ((x/d)/Zpos p =? x/(d*Zpos p)) = true.
Proof. intros; apply Z.eqb_eq; apply Z.div_div; lia. Qed.
Lemma nested_positive_positive : forall x (p q:positive),
  ((x/Zpos p)/Zpos q =? x/(Zpos p*Zpos q)) = true.
Proof. intros; apply nested_positive_law; lia. Qed.
Lemma nested_negative_positive : forall x (p q:positive),
  ((x/Zneg p)/Zpos q =? x/(Zneg p*Zpos q)) = true.
Proof. intros; apply nested_positive_law; lia. Qed.
Lemma positive_division_shift : forall x k (p:positive),
  ((x+k*Zpos p) / Zpos p =? x/Zpos p+k) = true.
Proof. intros; apply Z.eqb_eq; apply Z.div_add; lia. Qed.
Print Assumptions positive_division_shift.
Lemma positive_modulo_shift : forall x k (p:positive),
  ((x+k*Zpos p) mod Zpos p =? x mod Zpos p) = true.
Proof. intros; apply Z.eqb_eq; apply Z.mod_add; lia. Qed.
Print Assumptions positive_modulo_shift.
Lemma negative_division_shift : forall x k (p:positive),
  ((x+k*Zneg p) / Zneg p =? x/Zneg p+k) = true.
Proof. intros; apply Z.eqb_eq; apply Z.div_add; lia. Qed.
Print Assumptions negative_division_shift.
Lemma negative_modulo_shift : forall x k (p:positive),
  ((x+k*Zneg p) mod Zneg p =? x mod Zneg p) = true.
Proof. intros; apply Z.eqb_eq; apply Z.mod_add; lia. Qed.
Print Assumptions negative_modulo_shift.
(* Ground evaluation under an actual proved equality. The producer may choose
   the numeral, but both the equality and the calculation are proof arguments. *)
Lemma boolean_eq_true : forall b, Bool.eqb b true = true -> b = true.
Proof. intros []; simpl; congruence. Qed.
Lemma boolean_true_eq : forall b, Bool.eqb true b = true -> b = true.
Proof. intros []; simpl; congruence. Qed.
Print Assumptions boolean_eq_true.
Print Assumptions boolean_true_eq.
Lemma eqb_swap : forall x y, (x =? y) = true -> (y =? x) = true.
Proof. intros x y; rewrite Z.eqb_sym; trivial. Qed.
Lemma quotient_value : forall x y d v,
  (x =? y) = true -> (y/d =? v) = true -> (x/d =? v) = true.
Proof. intros x y d v H Hvalue; apply Z.eqb_eq in H; subst x; exact Hvalue. Qed.
Lemma remainder_value : forall x y d v,
  (x =? y) = true -> (y mod d =? v) = true -> (x mod d =? v) = true.
Proof. intros x y d v H Hvalue; apply Z.eqb_eq in H; subst x; exact Hvalue. Qed.
Print Assumptions eqb_swap.
Print Assumptions quotient_value.
Print Assumptions remainder_value.
Print Assumptions shift_laws.
Print Assumptions positive_shift_laws.
Print Assumptions negative_shift_laws.
Print Assumptions nested_positive_law.
Print Assumptions nested_positive_positive.
Print Assumptions nested_negative_positive.
Print Assumptions positive_laws.
Print Assumptions negative_laws.
Print Assumptions zero_laws.
End EunoiaDivision.
