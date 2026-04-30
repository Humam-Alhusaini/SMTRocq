From Stdlib Require Import NArith.
From Stdlib Require Import PArith.
From Stdlib Require Import PosDef.
From Stdlib Require Import Lia.

Require Import SMTCoq.SMTCoq.
Import BVList.BITVECTOR_LIST.

Open Scope positive.
Open Scope N.
Open Scope bool.
Open Scope list_scope.
Open Scope bv_scope.

Fixpoint pos_to_bits (p : positive) : list bool :=
  match p with
  | xH => true :: nil
  | xO p' => false :: pos_to_bits p'
  | xI p' => true :: pos_to_bits p'
  end.

Definition N_to_bits (n : N) : list bool :=
  match n with
  | N0 => nil
  | Npos p => pos_to_bits p end.

Axiom len_bv_n : 
  forall n, N.to_nat (N.size n) = length (N_to_bits n).

Fixpoint bits_to_N (lb : list bool) : N :=
  match lb with
  | nil => 0
  | b :: l' => (if b then 1 else 0) + 2 * bits_to_N l'
  end.

Axiom bits_n_eq :
  forall x y, N_to_bits x = N_to_bits y <-> x = y.

Axiom n_bits_eq :
  forall lb1 lb2, bits_to_N lb1 = bits_to_N lb2 <-> lb1 = lb2.

Axiom inverse_bits_n : 
  forall n, bits_to_N (N_to_bits n) = n.

Axiom inverse_n_bits : 
  forall lb, N_to_bits (bits_to_N lb) = lb.

Definition N_to_bv n := of_bits (N_to_bits n).
Definition _of_bits_n n := _of_bits (N_to_bits n).

Definition bv_to_N (size : N) (bv : bitvector size) := bits_to_N (bits bv).

Definition bv_size := BVList.RAWBITVECTOR_LIST.size.

Axiom bv_n_mod : forall n size, n mod 2 ^ size = bv_to_N size (_of_bits_n n size).
