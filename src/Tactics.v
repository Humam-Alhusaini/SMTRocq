(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2026                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Require Import PropToBool.
From Stdlib Require Import NArith.
From Ltac2 Require Import Ltac2.

Declare ML Module "coq-smtcoq.smtcoq".

Tactic Notation "reify" := reify.

Import BVList.BITVECTOR_LIST.

Ltac2 rewrite_n_bv () :=
  repeat (
    first [
      rewrite n_add_bv
    | rewrite n_sub_bv
    | rewrite n_mul_bv
    | rewrite n_and_bv
    | rewrite n_or_bv
    | rewrite n_xor_bv
    | rewrite n_shiftl_bv
    | rewrite n_shiftr_bv
    | rewrite n_ult_bv
    | rewrite n_bv_size
    | rewrite n_eq_bv
    | rewrite testbit_spec_
    | rewrite <- N.land_ones
    ]
  ).

Ltac2 Notation "picinae" :=
  ltac1:(prop2bool);
  rewrite_n_bv ();
  ltac1:(reify).


(*
   Local Variables:
   coq-load-path: ((rec "." "SMTCoq"))
   End:
*)
