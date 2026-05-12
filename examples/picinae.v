
Require Import NArith.
Require Import SMTCoq.SMTCoq.
From Ltac2 Require Import Ltac2.

Import BVList.BITVECTOR_LIST.

Open Scope N.

(* ------------------------------------------------------------------ *)
(* Concrete arithmetic (n_add_bv, n_sub_bv, n_mul_bv, n_eq_bv)       *)
(* ------------------------------------------------------------------ *)

Goal 2 + 3 = 5.
Proof. picinae. Admitted.

Goal 0 + 7 = 7.
Proof. picinae. Admitted.

Goal 10 - 3 = 7.
Proof. picinae. Admitted.

Goal 5 - 5 = 0.
Proof. picinae. Admitted.

Goal 3 * 4 = 12.
Proof. picinae. Admitted.

Goal 0 * 100 = 0.
Proof. picinae. Admitted.

Goal 6 * 7 = 42.
Proof. picinae. Admitted.

(* ------------------------------------------------------------------ *)
(* Concrete bitwise (n_and_bv, n_or_bv, n_xor_bv)                    *)
(* ------------------------------------------------------------------ *)

Goal N.land 0xFF 0x0F = 0x0F.
Proof. picinae. Admitted.

Goal N.land 0xFF 0 = 0.
Proof. picinae. Admitted.

Goal N.land 0xAA 0x55 = 0.
Proof. picinae. Admitted.

Goal N.lor 0xF0 0x0F = 0xFF.
Proof. picinae. Admitted.

Goal N.lor 0 0xAB = 0xAB.
Proof. picinae. Admitted.

Goal N.lxor 0xFF 0xFF = 0.
Proof. picinae. Admitted.

Goal N.lxor 0xF0 0x0F = 0xFF.
Proof. picinae. Admitted.

Goal N.lxor 0xAA 0x55 = 0xFF.
Proof. picinae. Admitted.

(* ------------------------------------------------------------------ *)
(* Concrete shifts (n_shiftl_bv, n_shiftr_bv)                        *)
(* ------------------------------------------------------------------ *)

Goal N.shiftl 1 4 = 16.
Proof. picinae. Admitted.

Goal N.shiftl 3 2 = 12.
Proof. picinae. Admitted.

Goal N.shiftl 1 0 = 1.
Proof. picinae. Admitted.

Goal N.shiftr 256 4 = 16.
Proof. picinae. Admitted.

Goal N.shiftr 12 2 = 3.
Proof. picinae. Admitted.

Goal N.shiftr 1 1 = 0.
Proof. picinae. Admitted.

(* ------------------------------------------------------------------ *)
(* One variable: additive identities (n_add_bv, n_sub_bv)            *)
(* ------------------------------------------------------------------ *)

(* x + 0 = x  (valid in 32-bit BV: bvadd(x, 0) = x) *)
Goal forall x : N, x + 0 = x.
Proof. picinae. Admitted.

(* 0 + x = x *)
Goal forall x : N, 0 + x = x.
Proof. picinae. Admitted.

(* x - 0 = x *)
Goal forall x : N, x - 0 = x.
Proof. picinae. Admitted.

(* x - x = 0 *)
Goal forall x : N, x - x = 0.
Proof. picinae. Admitted.

(* ------------------------------------------------------------------ *)
(* One variable: multiplicative identities (n_mul_bv)                *)
(* ------------------------------------------------------------------ *)

(* x * 0 = 0 *)
Goal forall x : N, x * 0 = 0.
Proof. picinae. Admitted.

(* x * 1 = x *)
Goal forall x : N, x * 1 = x.
Proof. picinae. Admitted.

(* x * 2 = x + x  (valid in BV modular arithmetic) *)
Goal forall x : N, x * 2 = x + x.
Proof. picinae. Admitted.

(* ------------------------------------------------------------------ *)
(* One variable: bitwise identities (n_and_bv, n_or_bv, n_xor_bv)   *)
(* ------------------------------------------------------------------ *)

(* x land x = x *)
Goal forall x : N, N.land x x = x.
Proof. picinae. Admitted.

(* x land 0 = 0 *)
Goal forall x : N, N.land x 0 = 0.
Proof. picinae. Admitted.

(* x lor x = x *)
Goal forall x : N, N.lor x x = x.
Proof. picinae. Admitted.

(* x lor 0 = x *)
Goal forall x : N, N.lor x 0 = x.
Proof. picinae. Admitted.

(* x lxor x = 0 *)
Goal forall x : N, N.lxor x x = 0.
Proof. picinae. Admitted.

(* x lxor 0 = x *)
Goal forall x : N, N.lxor x 0 = x.
Proof. picinae. Admitted.

(* ------------------------------------------------------------------ *)
(* One variable: shift identities (n_shiftl_bv, n_shiftr_bv)        *)
(* ------------------------------------------------------------------ *)

(* shiftl x 0 = x *)
Goal forall x : N, N.shiftl x 0 = x.
Proof. picinae. Admitted.

(* shiftr x 0 = x *)
Goal forall x : N, N.shiftr x 0 = x.
Proof. picinae. Admitted.

(* shiftl x 1 = x * 2  (valid in 32-bit BV) *)
Goal forall x : N, N.shiftl x 1 = x * 2.
Proof. picinae. Admitted.

(* ------------------------------------------------------------------ *)
(* Two variables: commutativity                                        *)
(* ------------------------------------------------------------------ *)

Goal forall x y : N, x + y = y + x.
Proof. picinae. Admitted.

Goal forall x y : N, x * y = y * x.
Proof. picinae. Admitted.

Goal forall x y : N, N.land x y = N.land y x.
Proof. picinae. Admitted.

Goal forall x y : N, N.lor x y = N.lor y x.
Proof. picinae. Admitted.

Goal forall x y : N, N.lxor x y = N.lxor y x.
Proof. picinae. Admitted.

(* ------------------------------------------------------------------ *)
(* Two variables: other identities                                     *)
(* ------------------------------------------------------------------ *)

(* (x + y) - y = x  (valid in BV: bvsub(bvadd(x,y), y) = x) *)
Goal forall x y : N, x + y - y = x.
Proof. picinae. Admitted.

(* x lxor y lxor y = x  (double XOR cancels) *)
Goal forall x y : N, N.lxor (N.lxor x y) y = x.
Proof. picinae. Admitted.

(* land(x,y) + lxor(x,y) = lor(x,y)  (bitwise decomposition identity) *)
Goal forall x y : N, N.land x y + N.lxor x y = N.lor x y.
Proof. picinae. Admitted.

(* ------------------------------------------------------------------ *)
(* Three variables: associativity                                      *)
(* ------------------------------------------------------------------ *)

Goal forall x y z : N, x + (y + z) = (x + y) + z.
Proof. picinae. Admitted.

Goal forall x y z : N, N.land x (N.land y z) = N.land (N.land x y) z.
Proof. picinae. Admitted.

Goal forall x y z : N, N.lor x (N.lor y z) = N.lor (N.lor x y) z.
Proof. picinae. Admitted.

Goal forall x y z : N, N.lxor x (N.lxor y z) = N.lxor (N.lxor x y) z.
Proof. picinae. Admitted.

(* ------------------------------------------------------------------ *)
(* Three variables: distributivity                                     *)
(* ------------------------------------------------------------------ *)

(* land distributes over lor *)
Goal forall x y z : N,
  N.land x (N.lor y z) = N.lor (N.land x y) (N.land x z).
Proof. picinae. Admitted.

(* lor distributes over land *)
Goal forall x y z : N,
  N.lor x (N.land y z) = N.land (N.lor x y) (N.lor x z).
Proof. picinae. Admitted.

(* ------------------------------------------------------------------ *)
(* De Morgan laws (using lxor with 0xFFFFFFFF as bitwise NOT)        *)
(* ------------------------------------------------------------------ *)

(* not(x and y) = not(x) or not(y) *)
Goal forall x y : N,
  N.lxor (N.land x y) 0xFFFFFFFF =
  N.lor (N.lxor x 0xFFFFFFFF) (N.lxor y 0xFFFFFFFF).
Proof. picinae. Admitted.

(* not(x or y) = not(x) and not(y) *)
Goal forall x y : N,
  N.lxor (N.lor x y) 0xFFFFFFFF =
  N.land (N.lxor x 0xFFFFFFFF) (N.lxor y 0xFFFFFFFF).
Proof. picinae. Admitted.

(* ------------------------------------------------------------------ *)
(* Comparison (n_ult_bv): concrete cases                             *)
(* ------------------------------------------------------------------ *)

(* 3 <? 5 = true *)
Goal N.ltb 3 5 = bv_ult (_N_to_bits 3 32) (_N_to_bits 5 32).
Proof. picinae. Admitted.

(* 10 <? 10 = false *)
Goal N.ltb 10 10 = bv_ult (_N_to_bits 10 32) (_N_to_bits 10 32).
Proof. picinae. Admitted.

(* ------------------------------------------------------------------ *)
(*  testbit                            *)
(* ------------------------------------------------------------------ *)
Search (N.testbit _ _ = _).

Goal N.testbit 5 1 = N.testbit 5 1.
Proof. picinae. Admitted.

Goal forall x, N.testbit x 1 = N.testbit x 1.
Proof. picinae. Admitted.

Goal forall x y, N.testbit x y = (N.land (N.shiftr x y) 1 =? 1).
Proof. picinae. Admitted.
(* ------------------------------------------------------------------ *)
(* False goals: exercise type-correct SMT generation for variables   *)
(* ------------------------------------------------------------------ *)

(* x = x + 1 is FALSE in both N and 32-bit BV *)
Goal forall x : N, x = x + 1.
Proof. picinae. Admitted.

(* x + 1 = x is FALSE *)
Goal forall x : N, x + 1 = x.
Proof. picinae. Admitted.

(* x * 2 = x is FALSE (unless x = 0) *)
Goal forall x : N, x * 2 = x.
Proof. picinae. Admitted.

(* x land y = x lor y is FALSE in general *)
Goal forall x y : N, N.land x y = N.lor x y.
Proof. picinae. Admitted.

(* x shiftl 1 = x is FALSE (unless x = 0) *)
Goal forall x : N, N.shiftl x 1 = x.
Proof. picinae. Admitted.
