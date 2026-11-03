(* Optional integration test against the separately owned local gate. *)
From Stdlib Require Import Uint63.
From SMTCoq.structures Require Import CompDecInstances.
From SMTCoq.checker Require Import MainChecker.
From EunoiaWitnessProbe Require Import EunoiaLocal.
Local Open Scope uint63_scope.

Definition witness_probe_types := PArray.make 0 unit_typ_compdec.
Definition witness_probe_functions : PArray.array (Terms.Atom.tval witness_probe_types) :=
  PArray.make 0 (@Terms.Atom.Tval witness_probe_types (nil, Terms.Typ.Tbool) true).
Definition witness_gate :=
  @EunoiaLocal.EunoiaLocal.gate witness_probe_types witness_probe_functions.

Declare ML Module "rocq-smtcoq.eunoia_witness_gate_probe".
Eunoia_witness_probe.
