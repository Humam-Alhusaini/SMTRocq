Require Import NArith.
Require Import ZArith.
Require Import PArith.
Require Import List.
Require Import Bool.

Require Import SMTCoq.SMTCoq.

Open Scope N.

Goal 2 + 3 = 5.
Proof. picinae. Admitted.

Goal forall
    (x y: Z)
    (f: Z -> Z),
    x = y + 1 -> f y = f (x - 1).
Proof. reify. Admitted.

Local Open Scope positive.
Local Open Scope N.
Local Open Scope bool.
Local Open Scope list_scope.
Local Open Scope bv_scope.

Goal 2 + 3 = 5.
Proof. reify. Admitted.


Goal 2 + 3 = 5.
Proof. reify. Admitted.

Goal (0 + 0 = 0)%N.
Proof. reify. Admitted.

Goal (1 * 1 = 1)%N.
Proof. reify. Admitted.

Goal (2 * 3 = 6)%N.
Proof. reify. Admitted.

Goal (5 - 3 = 2)%N.
Proof. reify. Admitted.

Goal (0 * 100 = 0)%N.
Proof. reify. Admitted.

Goal (1 + 0 = 1)%N.
Proof. reify. Admitted.

Goal (N.double 3 = 6)%N.
Proof. reify. Admitted.

Goal forall (x : N), (x + 0 = x)%N.
Proof. reify. Admitted.

Goal forall (x : N), (0 + x = x)%N.
Proof. reify. Admitted.

Goal forall (x y : N), (x + y = y + x)%N.
Proof. reify. Admitted.

Goal forall (x y z : N), (x + (y + z) = (x
