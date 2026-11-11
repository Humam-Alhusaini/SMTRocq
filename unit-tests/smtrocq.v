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

Lemma compiled_boolean_chain : forall (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Z), (x0 =? x1) && (x1 =? x2) && (x2 =? x3) && (x3 =? x4) && (x4 =? x5) && (x5 =? x6) && (x6 =? x7) && (x7 =? x8) && (x8 =? x9) && (x9 =? x10) && negb (x0 =? x10) = false.
Proof. smtrocq. Qed.
