From SMTCoq Require Import SMTCoq.
From SMTCoq.checker.eunoia Require Import EunoiaScopedAdapter.
From Stdlib Require Import Bool.

Section ExistingInstances.
  Variable A B : Type.
  Variable HA : CompDec A.
  Variable HB : CompDec B.

  Lemma backend_multiple_sorts (f : A -> B) (g : B -> A) (x y : A) :
    x = y -> g (f x) = g (f y).
  Proof using HA HB. cvc5_eunoia. Qed.

  Lemma backend_duplicate_root_proofs (f : A -> A) (x y z : A)
    (Hxy : x = y) (Hyz : y = z) : f x = f z.
  Proof using HA. cvc5_eunoia (Hxy, Hyz). Qed.
  Lemma backend_list_metadata_live (p : A -> bool) (x y : A) :
    x = y -> p x = true -> p y = true.
  Proof using HA. cvc5_eunoia. Qed.
End ExistingInstances.
Print Assumptions backend_multiple_sorts.
Print Assumptions backend_duplicate_root_proofs.
Print Assumptions backend_list_metadata_live.

Section MissingInstance.
  Variable A B : Type.
  Variable HA : CompDec A.
  Lemma backend_missing_intermediate_instance (f : A -> B) (g : B -> A) (x y : A) :
    x = y -> g (f x) = g (f y).
  Proof using HA.
    Fail cvc5_eunoia.
    intros H; now subst.
  Qed.
End MissingInstance.
