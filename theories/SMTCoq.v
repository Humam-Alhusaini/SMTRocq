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


(* Compatibility entry point. SMTRocq preserves the inherited SMTCoq tactics
   and public CVC5 tactics while using the separately maintained checker. *)
From SMTCoq Require Export SMTRocq.
