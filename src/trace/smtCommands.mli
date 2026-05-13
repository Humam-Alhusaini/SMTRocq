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

(* For extraction *)
val compute_roots : SmtAtom.Form.t list -> SmtAtom.Form.t SmtCertif.clause -> int list

val reify : unit -> CoqInterface.tactic
