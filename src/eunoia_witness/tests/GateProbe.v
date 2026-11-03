(* Optional integration test against the separately owned local gate. *)
From Stdlib Require Import Uint63 List Bool.
From SMTCoq.structures Require Import CompDecInstances.
From SMTCoq.checker Require Import MainChecker.
From EunoiaWitnessProbe Require Import EunoiaLocal.
Local Open Scope uint63_scope.

Definition witness_probe_types := PArray.make 0 unit_typ_compdec.
Fixpoint witness_function (args : list Terms.Typ.type) (result : Terms.Typ.type) :
  Terms.Typ.interp_ftype witness_probe_types (args,result) :=
  match args as xs return Terms.Typ.interp_ftype witness_probe_types (xs,result) with
  | nil => @CompDec.default_value _
      (@CompDec.inh_of_compdec _ (Terms.Typ.interp_compdec witness_probe_types result))
  | cons a xs => fun _ => witness_function xs result
  end.
Definition witness_value args result :=
  @Terms.Atom.Tval witness_probe_types (args,result) (witness_function args result).
Definition witness_gate funcs atoms forms cs c w :=
  Terms.Atom.wt witness_probe_types funcs atoms &&
  @EunoiaLocal.EunoiaLocal.gate witness_probe_types funcs atoms forms cs c w.

Declare ML Module "rocq-smtcoq.eunoia_witness_gate_probe".
Eunoia_witness_probe.
