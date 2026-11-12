From SMTCoq Require Import SMTRocq.
From SMTCoq.structures Require Import FArray.
From Stdlib Require Import Bool ZArith.
Local Open Scope Z_scope.
Lemma array_read_same : forall (a:FArray.farray Z Z) (i v:Z), FArray.select (FArray.store a i v) i = v.
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions array_read_same.
Lemma array_read_other : forall (a:FArray.farray Z Z) (i j v:Z), i<>j -> FArray.select (FArray.store a i v) j = FArray.select a j.
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions array_read_other.
Lemma array_overwrite : forall (a:FArray.farray Z Z) (i v w:Z), FArray.store (FArray.store a i v) i w=FArray.store a i w.
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions array_overwrite.
Lemma array_store_read : forall (a:FArray.farray Z Z) (i:Z), FArray.store a i (FArray.select a i)=a.
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions array_store_read.
Lemma array_store_commute : forall (a:FArray.farray Z Z) (i j v w:Z), i<>j -> FArray.store (FArray.store a i v) j w=FArray.store (FArray.store a j w) i v.
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions array_store_commute.
Lemma array_lia : forall (a:FArray.farray Z Z) (i v:Z), v>=0 -> FArray.select (FArray.store a i v) i>=0.
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions array_lia.
Lemma array_alias_read : forall (a b:FArray.farray Z Z) (i j:Z), a=b -> i=j -> FArray.select a i=FArray.select b j.
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions array_alias_read.
Lemma array_index_arithmetic : forall (a:FArray.farray Z Z) (i j v:Z), i+1<=j -> FArray.select (FArray.store a i v) j=FArray.select a j.
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions array_index_arithmetic.
Lemma array_arithmetic_alias : forall (a:FArray.farray Z Z) (i j v:Z), i<=j -> j<=i -> FArray.select (FArray.store a i v) j=v.
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions array_arithmetic_alias.
Lemma array_two_writes_read : forall (a:FArray.farray Z Z) (i j v w:Z), i<>j -> FArray.select (FArray.store (FArray.store a i v) j w) i=v.
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions array_two_writes_read.
Lemma array_value_arithmetic : forall (a:FArray.farray Z Z) (i x y:Z), x<=y -> FArray.select (FArray.store a i x) i<=y.
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions array_value_arithmetic.
Lemma array_distinct_indices : forall (a:FArray.farray Z Z) (i v:Z), FArray.select (FArray.store a i v) (i+1)=FArray.select a (i+1).
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions array_distinct_indices.
Lemma array_uf : forall (a:FArray.farray Z Z) (f:Z->Z) (i v:Z), f (FArray.select (FArray.store a i v) i)=f v.
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions array_uf.
Lemma array_nested_read : forall (a:FArray.farray Z (FArray.farray Z Z)) (b:FArray.farray Z Z) (i j:Z), FArray.select (FArray.select (FArray.store a i b) i) j=FArray.select b j.
Proof. Timeout 30 smtrocq. Qed.
Print Assumptions array_nested_read.
Example array_false_missing_disequality : True.
Proof.
 Fail assert (forall (a:FArray.farray Z Z) (i j v:Z), FArray.select (FArray.store a i v) j=FArray.select a j) by smtrocq.
 exact I.
Qed.
Print Assumptions array_false_missing_disequality.
Example array_false_value : True.
Proof.
 Fail assert (forall (a:FArray.farray Z Z) (i v w:Z), FArray.select (FArray.store a i v) i=w) by smtrocq.
 exact I.
Qed.
Print Assumptions array_false_value.
Example array_false_single_read : True.
Proof.
 Fail assert (forall (a b:FArray.farray Z Z) (i:Z), FArray.select a i=FArray.select b i -> a=b) by smtrocq.
 exact I.
Qed.
Print Assumptions array_false_single_read.
Example array_false_original : True.
Proof.
 Fail assert (forall (a:FArray.farray Z Z) (i v:Z), FArray.store a i v=a) by smtrocq.
 exact I.
Qed.
Print Assumptions array_false_original.
Example array_false_commute_alias : True.
Proof.
 Fail assert (forall (a:FArray.farray Z Z) (i v w:Z), FArray.store (FArray.store a i v) i w=FArray.store (FArray.store a i w) i v) by smtrocq.
 exact I.
Qed.
Print Assumptions array_false_commute_alias.
Example array_false_arithmetic_index : True.
Proof.
 Fail assert (forall (a:FArray.farray Z Z) (i j v:Z), i<=j -> FArray.select (FArray.store a i v) j=FArray.select a j) by smtrocq.
 exact I.
Qed.
Print Assumptions array_false_arithmetic_index.
