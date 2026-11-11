From SMTCoq Require Import SMTRocq.
From Stdlib Require Import Bool ZArith.
Local Open Scope Z_scope.
Lemma compiled_uf (A B:Type) (HA:CompDec A) (HB:CompDec B)
 (f:A->B) (x y:A):x=y->f x=f y.
Proof. smtrocq. Qed.
Lemma compiled_lia (x y:Z):x<=y->y<x+1->x=y.
Proof. smtrocq. Qed.
Lemma compiled_negative_literal (x:Z):x<= -3->x< -2.
Proof. smtrocq. Qed.
Lemma compiled_mixed (f:Z->Z)(x y:Z):x<=y->y<=x->f x=f y.
Proof. smtrocq. Qed.
Lemma compiled_division (x:Z):(x/3)*3+x mod 3=x.
Proof. smtrocq. Qed.
Lemma compiled_zero_division (x:Z):x/0=0.
Proof. smtrocq. Qed.
Lemma compiled_explicit_fact (x y:Z)(H:x<=y):x<y+1.
Proof. smtrocq H. Qed.
Lemma compiled_rejects_false_goals:True.
Proof.
 Fail assert(forall x:Z,x<0) by smtrocq.
 Fail assert(forall(f:Z->Z)(x y:Z),f x=f y->x=y) by smtrocq.
 exact I.
Qed.
