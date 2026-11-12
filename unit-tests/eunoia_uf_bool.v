(**************************************************************************)
(* Typed Boolean UF public integration. Every positive uses cvc5_eunoia. *)
(**************************************************************************)
From SMTCoq Require Import SMTRocq.
From Stdlib Require Import Bool ZArith.
Local Open Scope Z_scope.

Lemma bool_uf_original (f : bool -> bool) (a b : bool) : a = b -> f a = f b.
Proof. cvc5_eunoia. Qed.

Lemma bool_uf_integer_result (h : bool -> Z) (a b : bool) : a = b -> h a = h b.
Proof. cvc5_eunoia. Qed.

Lemma bool_uf_mixed (k : bool -> Z -> Z) (a b : bool) (x y : Z) : a = b -> x = y -> k a x = k b y.
Proof. cvc5_eunoia. Qed.

Lemma bool_uf_mixed_unchanged (k : bool -> Z -> Z) (a b : bool) (x : Z) : a = b -> k a x = k b x.
Proof. cvc5_eunoia. Qed.

Lemma bool_uf_nested (f g : bool -> bool) (a b : bool) : a = b -> f (g a) = f (g b).
Proof. cvc5_eunoia. Qed.

Lemma bool_uf_nested_integer (f : bool -> bool) (h : bool -> Z) (a b : bool) : a = b -> h (f a) = h (f b).
Proof. cvc5_eunoia. Qed.

Lemma bool_uf_false_inputs_with_edge (h : bool -> Z) (a b : bool) : a = b -> a = false -> b = false -> h a = h b.
Proof. cvc5_eunoia. Qed.

Lemma bool_uf_chain (f : bool -> bool) (a b c : bool) : a = b -> b = c -> f a = f c.
Proof. cvc5_eunoia. Qed.

Lemma bool_uf_conditional (f : bool -> bool) (a b : bool) : a <> b \/ f a = f b.
Proof. cvc5_eunoia. Qed.

Lemma bool_uf_compound_argument (f : bool -> bool) (a b c : bool) : a = b -> f (andb a c) = f (andb b c).
Proof. cvc5_eunoia. Qed.

Lemma bool_uf_nested_predicate (p : Z -> bool) (h : bool -> Z) (a b : bool) : a = b -> p (h a) = p (h b).
Proof. cvc5_eunoia. Qed.

(* Actual false statements: missing equality, injectivity, and distinct heads.
   Positive representation failures are recorded in boolean-uf-integration.md. *)
Example bool_uf_rejects_missing_edge : True.
Proof.
  Fail assert (forall (f : bool -> bool) (a b : bool), f a = f b) by cvc5_eunoia.
  exact I.
Qed.
Example bool_uf_rejects_injectivity : True.
Proof.
  Fail assert (forall (f : bool -> bool) (a b : bool), f a = f b -> a = b)
    by cvc5_eunoia.
  exact I.
Qed.
Example bool_uf_rejects_different_heads : True.
Proof.
  Fail assert (forall (f g : bool -> bool) (a b : bool), a = b -> f a = g b)
    by cvc5_eunoia.
  exact I.
Qed.

Print Assumptions bool_uf_original.
Print Assumptions bool_uf_integer_result.
Print Assumptions bool_uf_mixed.
Print Assumptions bool_uf_mixed_unchanged.
Print Assumptions bool_uf_nested.
Print Assumptions bool_uf_nested_integer.
Print Assumptions bool_uf_false_inputs_with_edge.
Print Assumptions bool_uf_chain.
Print Assumptions bool_uf_conditional.
Print Assumptions bool_uf_compound_argument.
Print Assumptions bool_uf_nested_predicate.
