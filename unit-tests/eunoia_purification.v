(* Public regressions for CPC purification. Every positive uses the checked tactic. *)
From SMTCoq Require Import SMTRocq.
From Stdlib Require Import Bool ZArith.

Lemma eunoia_purified_predicate (p : bool -> bool) (a b : bool) :
  a = b -> p a = true -> p b = true.
Proof. cvc5_eunoia. Qed.

Lemma eunoia_purified_negative_predicate (p : bool -> bool) (a b : bool) :
  a = b -> p a = false -> p b = false.
Proof. cvc5_eunoia. Qed.

Lemma eunoia_purified_disjunction (f : bool -> bool) (a b c : bool) :
  (a = b \/ a = c) -> (f a = f b \/ f a = f c).
Proof. cvc5_eunoia. Qed.

Lemma eunoia_false_inputs (h : bool -> Z) (a b : bool) :
  a = false -> b = false -> h a = h b.
Proof. cvc5_eunoia. Qed.

Lemma eunoia_false_argument (f : bool -> bool) (a : bool) :
  a = false -> f a = f false.
Proof. cvc5_eunoia. Qed.

Lemma eunoia_true_argument (f : bool -> bool) (a : bool) :
  true = a -> f a = f true.
Proof. cvc5_eunoia. Qed.

Lemma eunoia_tactic_reused_on_distinct_tables :
  (forall (f : Z -> Z) (x y : Z), x = y -> f x = f y) /\
  (forall x : Z, (x <= 0)%Z -> (x >= 1)%Z -> False).
Proof. split; cvc5_eunoia. Qed.

Example eunoia_purified_false_controls : True.
Proof.
  Fail assert (forall (p : bool -> bool) (a b : bool), p a = true -> p b = true)
    by cvc5_eunoia.
  Fail assert (forall (f : bool -> bool) (a b : bool), f a = f b -> a = b)
    by cvc5_eunoia.
  Fail assert (forall (f : bool -> bool) (a : bool), a = false -> f a = f true)
    by cvc5_eunoia.
  exact I.
Qed.

Print Assumptions eunoia_purified_predicate.
Print Assumptions eunoia_purified_negative_predicate.
Print Assumptions eunoia_purified_disjunction.
Print Assumptions eunoia_false_inputs.
Print Assumptions eunoia_false_argument.
Print Assumptions eunoia_true_argument.
Print Assumptions eunoia_tactic_reused_on_distinct_tables.
