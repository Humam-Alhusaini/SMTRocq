(* SMTCoq -- distributed under the CeCILL-C licence (see LICENSE). *)
From Stdlib Require Import List String.
From SMTCoq.checker.eunoia Require Import EoRuntime EoNameIndex.
Import ListNotations.
Open Scope string_scope.
Definition entries := [("",0);("$get",1);("$get_poly",2);("$get",3);("@nil",4)].
Definition index := Eval vm_compute in EoNameIndex.from_list entries.
Example exact_signature_keys :
 map (fun key=>EoNameIndex.lookup key index)
 ["";"$get";"$get_poly";"$get_polynomial";"$";"@nil";"unknown"]=
 [Some 0;Some 1;Some 2;None;None;Some 4;None].
Proof. vm_compute; reflexivity. Qed.
Example signature_lookup_refines_first_match : forall key,
 EoNameIndex.lookup key index=named key entries.
Proof. intro; exact (EoNameIndex.lookup_from_list _ entries key). Qed.
