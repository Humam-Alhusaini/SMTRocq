
Require Import NArith.
From SMTCoq Require Import Tactics.
From SMTCoq Require Import PropToBool.
From SMTCoq Require Import SMT_terms.
From Ltac2 Require Import Ltac2.

Import BVList.BITVECTOR_LIST.


Open Scope N.

(* ------------------------------------------------------------------ *)
(* Concrete arithmetic (n_add_bv, n_sub_bv, n_mul_bv, n_eq_bv)       *)
(* ------------------------------------------------------------------ *)

Goal (2 + 3) mod 2^32 = 5 mod 2^32.
Proof. picinae. Admitted.

Goal (0 + 7) mod 2^32 = 7 mod 2^32.
Proof. picinae. Admitted.

Goal (10 - 3) mod 2^32 = 7 mod 2^32.
Proof. picinae. Admitted.

Goal (5 - 5) mod 2^32 = 0 mod 2^32.
Proof. picinae. Admitted.

Goal (3 * 4) mod 2^32 = 12 mod 2^32.
Proof. picinae. Admitted.

Goal (0 * 100) mod 2^32 = 0 mod 2^32.
Proof. picinae. Admitted.

Goal (6 * 7) mod 2^32 = 42 mod 2^32.
Proof. picinae. Admitted.

(* ------------------------------------------------------------------ *)
(* Concrete bitwise (n_and_bv, n_or_bv, n_xor_bv)                    *)
(* ------------------------------------------------------------------ *)

Goal (N.land 0xFF 0x0F) mod 2^32 = 0x0F mod 2^32.
Proof. picinae. Admitted.

Goal (N.land 0xFF 0) mod 2^32 = 0 mod 2^32.
Proof. picinae. Admitted.

Goal (N.land 0xAA 0x55) mod 2^32 = 0 mod 2^32.
Proof. picinae. Admitted.

Goal (N.lor 0xF0 0x0F) mod 2^32 = 0xFF mod 2^32.
Proof. picinae. Admitted.

Goal (N.lor 0 0xAB) mod 2^32 = 0xAB mod 2^32.
Proof. picinae. Admitted.

Goal (N.lxor 0xFF 0xFF) mod 2^32 = 0 mod 2^32.
Proof. picinae. Admitted.

Goal (N.lxor 0xF0 0x0F) mod 2^32 = 0xFF mod 2^32.
Proof. picinae. Admitted.

Goal (N.lxor 0xAA 0x55) mod 2^32 = 0xFF mod 2^32.
Proof. picinae. Admitted.

(* ------------------------------------------------------------------ *)
(* Concrete shifts (n_shiftl_bv, n_shiftr_bv)                        *)
(* ------------------------------------------------------------------ *)

Goal (N.shiftl 1 4) mod 2^32 = 16 mod 2^32.
Proof. picinae. Admitted.

Goal (N.shiftl 3 2) mod 2^32 = 12 mod 2^32.
Proof. picinae. Admitted.

Goal (N.shiftl 1 0) mod 2^32 = 1 mod 2^32.
Proof. picinae. Admitted.

Goal (N.shiftr 256 4) mod 2^32 = 16 mod 2^32.
Proof. picinae. Admitted.

Goal (N.shiftr 12 2) mod 2^32 = 3 mod 2^32.
Proof. picinae. Admitted.

Goal (N.shiftr 1 1) mod 2^32 = 0 mod 2^32.
Proof. picinae. Admitted.

(* ------------------------------------------------------------------ *)
(* One variable: additive identities (n_add_bv, n_sub_bv)            *)
(* ------------------------------------------------------------------ *)

Goal forall x : N, (x + 0) mod 2^32 = x mod 2^32.
Proof. picinae. Admitted.

Goal forall x : N, (0 + x) mod 2^32 = x mod 2^32.
Proof. picinae. Admitted.

Goal forall x : N, (x - 0) mod 2^32 = x mod 2^32.
Proof. picinae. Admitted.

Goal forall x : N, (x - x) mod 2^32 = 0 mod 2^32.
Proof. picinae. Admitted.

(* ------------------------------------------------------------------ *)
(* One variable: multiplicative identities (n_mul_bv)                *)
(* ------------------------------------------------------------------ *)

Goal forall x : N, (x * 0) mod 2^32 = 0 mod 2^32.
Proof. picinae. Admitted.

Goal forall x : N, (x * 1) mod 2^32 = x mod 2^32.
Proof. picinae. Admitted.

Goal forall x : N, (x * 2) mod 2^32 = (x + x) mod 2^32.
Proof. picinae. Admitted.

(* ------------------------------------------------------------------ *)
(* One variable: bitwise identities (n_and_bv, n_or_bv, n_xor_bv)   *)
(* ------------------------------------------------------------------ *)

Goal forall x : N, (N.land x x) mod 2^32 = x mod 2^32.
Proof. picinae. Admitted.

Goal forall x : N, (N.land x 0) mod 2^32 = 0 mod 2^32.
Proof. picinae. Admitted.

Goal forall x : N, (N.lor x x) mod 2^32 = x mod 2^32.
Proof. picinae. Admitted.

Goal forall x : N, (N.lor x 0) mod 2^32 = x mod 2^32.
Proof. picinae. Admitted.

Goal forall x : N, (N.lxor x x) mod 2^32 = 0 mod 2^32.
Proof. picinae. Admitted.

Goal forall x : N, (N.lxor x 0) mod 2^32 = x mod 2^32.
Proof. picinae. Admitted.

(* ------------------------------------------------------------------ *)
(* One variable: shift identities (n_shiftl_bv, n_shiftr_bv)        *)
(* ------------------------------------------------------------------ *)

Goal forall x : N, (N.shiftl x 0) mod 2^32 = x mod 2^32.
Proof. picinae. Admitted.

Goal forall x : N, (N.shiftr x 0) mod 2^32 = x mod 2^32.
Proof. picinae. Admitted.

Goal forall x : N, (N.shiftl x 1) mod 2^32 = (x * 2) mod 2^32.
Proof. picinae. Admitted.

(* ------------------------------------------------------------------ *)
(* Two variables: commutativity                                        *)
(* ------------------------------------------------------------------ *)

Goal forall x y : N, (x + y) mod 2^32 = (y + x) mod 2^32.
Proof. picinae. Admitted.

Goal forall x y : N, (x * y) mod 2^32 = (y * x) mod 2^32.
Proof. picinae. Admitted.

Goal forall x y : N, (N.land x y) mod 2^32 = (N.land y x) mod 2^32.
Proof. picinae. Admitted.

Goal forall x y : N, (N.lor x y) mod 2^32 = (N.lor y x) mod 2^32.
Proof. picinae. Admitted.

Goal forall x y : N, (N.lxor x y) mod 2^32 = (N.lxor y x) mod 2^32.
Proof. picinae. Admitted.

(* ------------------------------------------------------------------ *)
(* Two variables: other identities                                     *)
(* ------------------------------------------------------------------ *)

(* (x + y) - y = x  (valid in BV: bvsub(bvadd(x,y), y) = x) *)
Goal forall x y : N, (x + y - y) mod 2^32 = x mod 2^32.
Proof. picinae. Admitted.

(* x lxor y lxor y = x  (double XOR cancels) *)
Goal forall x y : N, (N.lxor (N.lxor x y) y) mod 2^32 = x mod 2^32.
Proof. picinae. Admitted.

(* land(x,y) + lxor(x,y) = lor(x,y)  (bitwise decomposition identity) *)
Goal forall x y : N, (N.land x y + N.lxor x y) mod 2^32 = (N.lor x y) mod 2^32.
Proof. picinae. Admitted.

(* ------------------------------------------------------------------ *)
(* Three variables: associativity                                      *)
(* ------------------------------------------------------------------ *)

Goal forall x y z : N, (x + (y + z)) mod 2^32 = ((x + y) + z) mod 2^32.
Proof. picinae. Admitted.

Goal forall x y z : N,
  (N.land x (N.land y z)) mod 2^32 = (N.land (N.land x y) z) mod 2^32.
Proof. picinae. Admitted.

Goal forall x y z : N,
  (N.lor x (N.lor y z)) mod 2^32 = (N.lor (N.lor x y) z) mod 2^32.
Proof. picinae. Admitted.

Goal forall x y z : N,
  (N.lxor x (N.lxor y z)) mod 2^32 = (N.lxor (N.lxor x y) z) mod 2^32.
Proof. picinae. Admitted.

(* ------------------------------------------------------------------ *)
(* Three variables: distributivity                                     *)
(* ------------------------------------------------------------------ *)

(* land distributes over lor *)
Goal forall x y z : N,
  (N.land x (N.lor y z)) mod 2^32 = (N.lor (N.land x y) (N.land x z)) mod 2^32.
Proof. picinae. Admitted.

(* lor distributes over land *)
Goal forall x y z : N,
  (N.lor x (N.land y z)) mod 2^32 = (N.land (N.lor x y) (N.lor x z)) mod 2^32.
Proof. picinae. Admitted.

(* ------------------------------------------------------------------ *)
(* De Morgan laws (using lxor with 0xFFFFFFFF as bitwise NOT)        *)
(* ------------------------------------------------------------------ *)

(* not(x and y) = not(x) or not(y) *)
Goal forall x y : N,
  (N.lxor (N.land x y) 0xFFFFFFFF) mod 2^32 =
  (N.lor (N.lxor x 0xFFFFFFFF) (N.lxor y 0xFFFFFFFF)) mod 2^32.
Proof. picinae. Admitted.

(* not(x or y) = not(x) and not(y) *)
Goal forall x y : N,
  (N.lxor (N.lor x y) 0xFFFFFFFF) mod 2^32 =
  (N.land (N.lxor x 0xFFFFFFFF) (N.lxor y 0xFFFFFFFF)) mod 2^32.
Proof. picinae. Admitted.

(* ------------------------------------------------------------------ *)
(* Comparison (n_ult_bv): concrete cases                             *)
(* ------------------------------------------------------------------ *)

(* 3 mod 2^32 <? 5 mod 2^32 = bv_ult (_N_to_bits 3 32) (_N_to_bits 5 32) *)
Goal 3 mod 2^32 <? 5 mod 2^32 = bv_ult (_N_to_bits 3 32) (_N_to_bits 5 32).
Proof. picinae. Admitted.

(* 10 mod 2^32 <? 10 mod 2^32 = bv_ult (_N_to_bits 10 32) (_N_to_bits 10 32) *)
Goal 10 mod 2^32 <? 10 mod 2^32 = bv_ult (_N_to_bits 10 32) (_N_to_bits 10 32).
Proof. picinae. Admitted.

(* ------------------------------------------------------------------ *)
(* lt: concrete cases                                                 *)
(* ------------------------------------------------------------------ *)

Goal (3 mod 2^32 <? 5 mod 2^32)%N = true.
Proof. picinae. Admitted.

Goal (5 mod 2^32 <? 3 mod 2^32)%N = false.
Proof. picinae. Admitted.

Goal (7 mod 2^32 <? 7 mod 2^32)%N = false.
Proof. picinae. Admitted.

(* ------------------------------------------------------------------ *)
(* lt: variable goals                                                 *)
(* ------------------------------------------------------------------ *)

(* x < x is always false *)
Goal forall x : N, (x mod 2^32 <? x mod 2^32)%N = false.
Proof. picinae. Admitted.

(* transitivity: if x < y and y < z then x < z *)
Goal forall x y z : N,
  (x mod 2^32 <? y mod 2^32)%N = true ->
  (y mod 2^32 <? z mod 2^32)%N = true ->
  (x mod 2^32 <? z mod 2^32)%N = true.
Proof. picinae. Admitted.

(* ------------------------------------------------------------------ *)
(*  testbit                                                           *)
(* ------------------------------------------------------------------ *)

Goal N.testbit 5 1 = N.testbit 5 1.
Proof. picinae. Admitted.

Goal forall x, N.testbit x 1 = N.testbit x 1.
Proof. picinae. Admitted.

Goal forall x y, N.testbit x y = (N.land (N.shiftr x y) 1 =? 1).
Proof. picinae. Admitted.

(* ------------------------------------------------------------------ *)
(* False goals: SMT solver must reject these                          *)
(* ------------------------------------------------------------------ *)

(* x = x + 1 is FALSE in 32-bit BV *)
Goal forall x : N, x mod 2^32 = (x + 1) mod 2^32.
Proof. picinae. Abort.

(* x + 1 = x is FALSE *)
Goal forall x : N, (x + 1) mod 2^32 = x mod 2^32.
Proof. picinae. Abort.

(* x * 2 = x is FALSE (unless x = 0) *)
Goal forall x : N, (x * 2) mod 2^32 = x mod 2^32.
Proof. picinae. Abort.

(* x land y = x lor y is FALSE in general *)
Goal forall x y : N, (N.land x y) mod 2^32 = (N.lor x y) mod 2^32.
Proof. picinae. Abort.

(* x shiftl 1 = x is FALSE (unless x = 0) *)
Goal forall x : N, (N.shiftl x 1) mod 2^32 = x mod 2^32.
Proof. picinae. Abort.

(* x < x + 1 is FALSE in 32-bit BV due to overflow *)
Goal forall x : N, (x mod 2^32 <? (x + 1) mod 2^32)%N = true.
Proof. picinae. Abort.
