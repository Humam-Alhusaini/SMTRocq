From SMTCoq Require Import SMTCoq.
From Stdlib Require Import Bool ZArith.
Declare ML Module "rocq-smtcoq.eunoia_backend_test".
Local Open Scope Z_scope.

(* A failed tactic never supplies a proof of the false statement. *)
Lemma false_controls : True.
Proof.
  Fail assert ((0 : Z) = 1) by cvc5_eunoia.
  Fail assert (forall (A : Type) (HA : CompDec A)
    (f : A -> A) (x y : A), f x = f y -> x = y) by cvc5_eunoia.
  exact I.
Qed.
Print Assumptions false_controls.

(* Existing integration-plugin mutations: changed source answer, premise and
   root, missing semantic evidence, and a corrupted supported unused step. *)
Lemma source_controls (x : Z) : (x + 0 =? x) = true.
Proof.
  Fail backend_lia_bad_coefficient.
  Fail backend_lia_bad_premise.
  Fail backend_lia_bad_conclusion.
  Fail backend_lia_bad_root.
  backend_lia_replay.
Qed.
Print Assumptions source_controls.

Lemma local_controls (p : bool) : p = p.
Proof.
  Fail backend_bad_gate.
  Fail backend_bad_unused.
  backend_replay.
Qed.
Print Assumptions local_controls.
