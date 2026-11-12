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


(* SMTRocq extends the inherited SMTCoq theories with the CVC5 backend.
   The external Eunoia checker remains a separately maintained dependency. *)
From Stdlib Require Export Uint63 List.
From Trakt Require Export Trakt.

From SMTCoq.structures Require Export CompDecInstances.
From SMTCoq.checker.fol Require Export State Terms.
From SMTCoq.checker Require Export MainChecker.
From SMTCoq.checker.eunoia Require Import EunoiaMemo.
From SMTCoq.checker.eunoia Require Import EunoiaModelDagCheck EunoiaCertificate.
From SMTCoq.tactics Require Export Tactics Cvc5 DatabaseTrakt Conversion.

Export Atom Form Sat_Checker Cnf_Checker Euf_Checker.
