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
From Stdlib Require Import Uint63 List Bool ZArith.
Require Import PArray SMTCoq.State SMTCoq.SMT_terms SMTCoq.Trace SMT_classes_instances QInst.
From Ltac2 Require Import Ltac2.

Declare ML Module "coq-smtcoq.smtcoq".

Tactic Notation "reify" := prop2bool; reify.

Import BVList.BITVECTOR_LIST.
Open Scope N.

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
