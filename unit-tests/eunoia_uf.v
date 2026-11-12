(**************************************************************************)
(*     SMTCoq -- distributed under the terms of the CeCILL-C licence       *)
(**************************************************************************)

From SMTCoq Require Import SMTRocq.
From SMTCoq.checker.eunoia Require Import EunoiaScopedAdapter.
From Stdlib Require Import Bool.

(* Every positive proof uses the public checked tactic and production search.
   The carriers are abstract; their equality decision procedures are ordinary
   generalized arguments, as in verit_tactics.v. *)
Section AbstractUF.
  Variable A : Type.
  Variable HA : CompDec A.

  Lemma eunoia_uf_symmetry (x y : A) : x = y -> y = x.
  Proof using HA. cvc5_eunoia. Qed.

  Lemma eunoia_uf_transitivity (x y z : A) : x = y -> y = z -> x = z.
  Proof using HA. cvc5_eunoia. Qed.

  Lemma eunoia_uf_chain (a b c d e : A) :
    a = b -> c = b -> c = d -> e = d -> a = e.
  Proof using HA. cvc5_eunoia. Qed.

  Lemma eunoia_uf_unary (f : A -> A) (x y : A) : x = y -> f x = f y.
  Proof using HA. cvc5_eunoia. Qed.

  Lemma eunoia_uf_nested (f g : A -> A) (x y z : A) :
    x = y -> y = z -> f (g (f x)) = f (g (f z)).
  Proof using HA. cvc5_eunoia. Qed.

  Lemma eunoia_uf_binary (f : A -> A -> A) (a b c d : A) :
    a = b -> c = d -> f a c = f b d.
  Proof using HA. cvc5_eunoia. Qed.

  Lemma eunoia_uf_binary_unchanged (f : A -> A -> A) (a b c : A) :
    a = b -> f a c = f b c.
  Proof using HA. cvc5_eunoia. Qed.

  Lemma eunoia_uf_binary_nested (f : A -> A -> A) (g : A -> A)
      (a b c d : A) :
    a = b -> c = d -> f (g a) (f a c) = f (g b) (f b d).
  Proof using HA. cvc5_eunoia. Qed.

  Lemma eunoia_uf_predicate_positive (p : A -> bool) (x y : A) :
    x = y -> p x = true -> p y = true.
  Proof using HA. cvc5_eunoia. Qed.

  Lemma eunoia_uf_predicate_negative (p : A -> bool) (x y : A) :
    x = y -> p x = false -> p y = false.
  Proof using HA. cvc5_eunoia. Qed.

  Lemma eunoia_uf_predicate_boolean (p : A -> bool) (x y : A) :
    x = y -> p x = p y.
  Proof using HA. cvc5_eunoia. Qed.

  Lemma eunoia_uf_binary_predicate (p : A -> A -> bool) (a b c d : A) :
    a = b -> c = d -> p a c = true -> p b d = true.
  Proof using HA. cvc5_eunoia. Qed.

  Lemma eunoia_uf_disequality (x y z : A) :
    x = y -> y = z -> x <> z -> False.
  Proof using HA. cvc5_eunoia. Qed.

  Lemma eunoia_uf_congruence_conflict (f : A -> A) (x y : A) :
    x = y -> f x <> f y -> False.
  Proof using HA. cvc5_eunoia. Qed.

  Lemma eunoia_uf_disjunctive_root (f : A -> A) (x y z : A) :
    (x = y \/ x = z) -> f x <> f y -> f x = f z.
  Proof using HA. cvc5_eunoia. Qed.

  Lemma eunoia_uf_nonunit_consequence (f : A -> A) (x y z : A) :
    (x = y \/ x = z) -> (f x = f y \/ f x = f z).
  Proof using HA. cvc5_eunoia. Qed.

  Lemma eunoia_uf_equality_predicate (x y z : A) :
    x = y -> ((x = z) <-> (y = z)).
  Proof using HA. cvc5_eunoia. Qed.

  Lemma eunoia_uf_supplied_hypothesis (f : A -> A) (x y z : A)
      (Hxy : x = y) (Hyz : y = z) : f x = f z.
  Proof using HA. cvc5_eunoia (Hxy, Hyz). Qed.

  Example eunoia_uf_rejects_unrelated_predicate : True.
  Proof using HA.
    Fail assert (forall (p : A -> bool) (x y : A), p x = p y)
      by cvc5_eunoia.
    exact I.
  Qed.

  Example eunoia_uf_rejects_injectivity : True.
  Proof using HA.
    Fail assert (forall (f : A -> A) (x y : A), f x = f y -> x = y)
      by cvc5_eunoia.
    exact I.
  Qed.
End AbstractUF.

Section MultipleSorts.
  Variable A B : Type.
  Variable HA : CompDec A.
  Variable HB : CompDec B.

  Lemma eunoia_uf_multiple_sorts (f : A -> B) (g : B -> A) (x y : A) :
    x = y -> g (f x) = g (f y).
  Proof using HA HB. cvc5_eunoia. Qed.

  Lemma eunoia_uf_mixed_arguments (f : A -> B -> A) (x y : A) (a b : B) :
    x = y -> a = b -> f x a = f y b.
  Proof using HA HB. cvc5_eunoia. Qed.
End MultipleSorts.

Lemma eunoia_uf_boolean_transitivity (a b c : bool) :
  a = b -> b = c -> a = c.
Proof. cvc5_eunoia. Qed.

(* Keep a proof-local carrier universe, as in the quantified benchmark. *)
Lemma eunoia_uf_quantified_carrier :
  forall (A : Type) (HA : CompDec A) (f : A -> A) (x y : A),
    x = y -> f x = f y.
Proof. cvc5_eunoia. Qed.

Print Assumptions eunoia_uf_symmetry.
Print Assumptions eunoia_uf_transitivity.
Print Assumptions eunoia_uf_chain.
Print Assumptions eunoia_uf_unary.
Print Assumptions eunoia_uf_nested.
Print Assumptions eunoia_uf_binary.
Print Assumptions eunoia_uf_binary_unchanged.
Print Assumptions eunoia_uf_binary_nested.
Print Assumptions eunoia_uf_predicate_positive.
Print Assumptions eunoia_uf_predicate_negative.
Print Assumptions eunoia_uf_predicate_boolean.
Print Assumptions eunoia_uf_binary_predicate.
Print Assumptions eunoia_uf_disequality.
Print Assumptions eunoia_uf_congruence_conflict.
Print Assumptions eunoia_uf_disjunctive_root.
Print Assumptions eunoia_uf_nonunit_consequence.
Print Assumptions eunoia_uf_equality_predicate.
Print Assumptions eunoia_uf_supplied_hypothesis.
Print Assumptions eunoia_uf_multiple_sorts.
Print Assumptions eunoia_uf_mixed_arguments.
Print Assumptions eunoia_uf_boolean_transitivity.
Print Assumptions eunoia_uf_quantified_carrier.

(* Integer-sorted UF must not invoke arithmetic search for Boolean rewriting. *)
From Stdlib Require Import ZArith.
Section IntegerSortedUF.
Local Open Scope Z_scope.
Lemma eunoia_uf_integer_boolean_chain : forall (a b c d e f : Z),
  (a =? b) && (b =? c) && (c =? d) && (c =? e) && (e =? f) && negb (a =? f) = false.
Proof. cvc5_eunoia. Qed.
Print Assumptions eunoia_uf_integer_boolean_chain.
Example eunoia_uf_integer_missing_link : True.
Proof.
  Fail assert (forall (a b c d e f : Z),
    (a =? b) && (b =? c) && (c =? d) && (c =? e) && negb (a =? f) = false)
    by cvc5_eunoia.
  exact I.
Qed.
Print Assumptions eunoia_uf_integer_missing_link.
End IntegerSortedUF.
