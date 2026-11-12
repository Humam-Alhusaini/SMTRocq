From SMTCoq Require Import SMTRocq.
From SMTCoq.structures Require Import FArray.
From Stdlib Require Import Bool ZArith.
Local Open Scope Z_scope.
Lemma abs_nonnegative : forall x:Z, 0 <= Z.abs x.
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions abs_nonnegative.
Lemma abs_opposite : forall x:Z, Z.abs (-x) = Z.abs x.
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions abs_opposite.
Lemma abs_triangle : forall x y:Z, Z.abs (x+y) <= Z.abs x + Z.abs y.
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions abs_triangle.
Lemma min_bound : forall x y:Z, Z.min x y <= x.
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions min_bound.
Lemma max_choice : forall x y:Z, x<=y -> Z.max x y=y.
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions max_choice.
Lemma min_max_sum : forall x y:Z, Z.min x y + Z.max x y = x+y.
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions min_max_sum.
Lemma symbolic_mod_positive : forall x d:Z, 0<d -> 0<=x mod d<d.
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions symbolic_mod_positive.
Lemma symbolic_mod_negative : forall x d:Z, d<0 -> d<x mod d<=0.
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions symbolic_mod_negative.
Lemma symbolic_zero_divisor : forall x d:Z, d=0 -> x/d=0.
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions symbolic_zero_divisor.
Lemma known_divisor : forall x d:Z, d=3 -> x mod d<3.
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions known_divisor.
Lemma abs_zero : forall x:Z, Z.abs x=0 -> x=0.
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions abs_zero.
Lemma abs_bounds : forall x:Z, -Z.abs x<=x<=Z.abs x.
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions abs_bounds.
Lemma abs_distance : forall x y:Z, Z.abs (x-y)=Z.abs (y-x).
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions abs_distance.
Lemma abs_uf : forall (f:Z->Z) (x:Z), f (Z.abs (-x))=f (Z.abs x).
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions abs_uf.
Lemma min_commute : forall x y:Z, Z.min x y=Z.min y x.
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions min_commute.
Lemma max_bound : forall x y:Z, y<=Z.max x y.
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions max_bound.
Lemma max_commute : forall x y:Z, Z.max x y=Z.max y x.
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions max_commute.
Lemma min_max_order : forall x y:Z, Z.min x y<=Z.max x y.
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions min_max_order.
Lemma sign_negative : forall x:Z, x<0 -> Z.sgn x = -1.
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions sign_negative.
Lemma sign_zero : forall x:Z, x=0 -> Z.sgn x=0.
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions sign_zero.
Lemma sign_positive : forall x:Z, 0<x -> Z.sgn x=1.
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions sign_positive.
Lemma sign_bounds : forall x:Z, -1<=Z.sgn x<=1.
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions sign_bounds.
Lemma symbolic_zero_remainder : forall x d:Z, d=0 -> x mod d=x.
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions symbolic_zero_remainder.
Lemma known_divisor_reverse : forall x d:Z, 3=d -> 0<=x mod d<3.
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions known_divisor_reverse.
Lemma known_negative_divisor : forall x d:Z, d= -3 -> -3<x mod d<=0.
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions known_negative_divisor.
Lemma known_divisor_expression : forall x d:Z, d=1+2 -> x mod d<3.
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions known_divisor_expression.
Lemma known_divisor_quotient : forall x d:Z, d=3 -> x=7 -> x/d=2.
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions known_divisor_quotient.
Lemma known_divisor_uf : forall (f:Z->Z) (x d:Z), d=3 -> f (x mod d)=f (x mod 3).
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions known_divisor_uf.
Example false_abs_identity : True.
Proof.
 Fail assert (forall x:Z, Z.abs x=x) by smtrocq.
 exact I.
Qed.
Print Assumptions false_abs_identity.
Example false_abs_strict : True.
Proof.
 Fail assert (forall x:Z, 0<Z.abs x) by smtrocq.
 exact I.
Qed.
Print Assumptions false_abs_strict.
Example false_min_choice : True.
Proof.
 Fail assert (forall x y:Z, Z.min x y=x) by smtrocq.
 exact I.
Qed.
Print Assumptions false_min_choice.
Example false_max_choice : True.
Proof.
 Fail assert (forall x y:Z, Z.max x y=x) by smtrocq.
 exact I.
Qed.
Print Assumptions false_max_choice.
Example false_sign_positive : True.
Proof.
 Fail assert (forall x:Z, Z.sgn x=1) by smtrocq.
 exact I.
Qed.
Print Assumptions false_sign_positive.
Example false_mod_negative : True.
Proof.
 Fail assert (forall x d:Z, d<0 -> 0<=x mod d) by smtrocq.
 exact I.
Qed.
Print Assumptions false_mod_negative.
Example false_mod_strict : True.
Proof.
 Fail assert (forall x d:Z, 0<d -> 0<x mod d) by smtrocq.
 exact I.
Qed.
Print Assumptions false_mod_strict.
Example false_mod_no_sign : True.
Proof.
 Fail assert (forall x d:Z, x mod d<d) by smtrocq.
 exact I.
Qed.
Print Assumptions false_mod_no_sign.
Example false_zero_mod : True.
Proof.
 Fail assert (forall x d:Z, d=0 -> x mod d=0) by smtrocq.
 exact I.
Qed.
Print Assumptions false_zero_mod.
Example false_divisor_link : True.
Proof.
 Fail assert (forall x d e:Z, e=3 -> x mod d<3) by smtrocq.
 exact I.
Qed.
Print Assumptions false_divisor_link.
Example false_known_quotient : True.
Proof.
 Fail assert (forall x d:Z, d=3 -> x=7 -> x/d=3) by smtrocq.
 exact I.
Qed.
Print Assumptions false_known_quotient.
