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

Lemma backend_forall_carrier : forall (A : Type) (HA : CompDec A)
  (f : A -> A) (x y : A), x = y -> f x = f y.
Proof. cvc5_eunoia. Qed.
Print Assumptions backend_forall_carrier.

Lemma backend_forall_carrier_chain : forall (A : Type) (HA : CompDec A)
  (f : A -> A) (x y z : A), x = y -> y = z -> f x = f z.
Proof. cvc5_eunoia. Qed.
Print Assumptions backend_forall_carrier_chain.

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

(* The benchmark's UF-shaped formula has integer carriers, so cvc5 also
   uses generated arithmetic normalization within its actual CPC proof. *)
From Stdlib Require Import ZArith.
Local Open Scope Z_scope.
Lemma backend_uf_integer_carrier (x y z : Z) (f : Z -> Z) :
  (x =? y) && (y =? z) && negb (f x =? f z) = false.
Proof. cvc5_eunoia. Qed.
Print Assumptions backend_uf_integer_carrier.
