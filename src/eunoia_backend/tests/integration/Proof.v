From Stdlib Require Import Bool String List.
From SMTCoq.checker.eunoia Require Import EunoiaAdapter EunoiaLocal EunoiaTactic.
Declare ML Module "rocq-smtcoq.eunoia_backend_test".

Lemma replay_reflexive (p:bool) : p = p.
Proof. backend_replay. Qed.
Print Assumptions replay_reflexive.

Lemma replay_with_lemma (p:bool) (hp:p=true) : p = p.
Proof. backend_with_lemma. Qed.
Print Assumptions replay_with_lemma.

Lemma replay_true (p:bool) : Bool.eqb p p = true.
Proof. backend_replay. Qed.
Print Assumptions replay_true.

Lemma replay_false (p:bool) : negb (Bool.eqb p p) = false.
Proof. backend_replay. Qed.
Print Assumptions replay_false.

Goal forall p:bool, p = p.
Proof.
  intros p.
  Fail backend_corrupted.
  Fail backend_bad_gate.
  Fail backend_bad_unused.
  (* The initial generated fragment lacks cvc5's evaluate rule. *)
  Fail backend_live.
  backend_replay.
Qed.
