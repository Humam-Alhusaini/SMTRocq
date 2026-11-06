(* SMTCoq -- distributed under the CeCILL-C licence (see LICENSE). *)
From Stdlib Require Import List String Bool Arith.
From SMTCoq.checker.eunoia Require Import EoSyntax EoRuntime EoCheckedMemo.
Import ListNotations EoCheckedMemo.
Open Scope string_scope.
Definition identity_program := {| program_binders := []; program_inputs := [PVar 0];
 program_output := PVar 0; program_cases := [{|case_patterns := [PVar 0]; case_body := EVar 0|}] |}.
Definition constant_program := {| program_binders := []; program_inputs := [];
 program_output := PSymbol "Bool"; program_cases := [{|case_patterns := []; case_body := ESymbol "true"|}] |}.
Definition loop_program := {| program_binders := []; program_inputs := [];
 program_output := PSymbol "Bool"; program_cases := [{|case_patterns := []; case_body := ECall "loop" []|}] |}.
Definition demo_programs := [("id",identity_program);("const",constant_program);("loop",loop_program)].
Definition demo_check budget entries e := checked_evaluate (closed_nil []) no_extension [] budget
 (fun _ => None) demo_programs entries [] e.
Example cache_identity : demo_check 8 [Entry 1 "id" [Symbol "x"] (Symbol "x")]
 (ECall "id" [ESymbol "x"]) = Some (Symbol "x").
Proof. vm_compute; reflexivity. Qed.
Example cache_wrong_value : demo_check 8 [Entry 1 "id" [Symbol "x"] (Symbol "y")]
 (ECall "id" [ESymbol "x"]) = None.
Proof. vm_compute; reflexivity. Qed.
Example cache_wrong_arguments : demo_check 8 [Entry 1 "id" [Symbol "y"] (Symbol "x")]
 (ECall "id" [ESymbol "x"]) = None.
Proof. vm_compute; reflexivity. Qed.
Example cache_cannot_bypass_fuel : demo_check 1 [Entry 0 "const" [] (Symbol "true")]
 (ECall "const" []) = None.
Proof. vm_compute; reflexivity. Qed.
Example cache_unused_corruption : demo_check 8 [Entry 1 "id" [Symbol "x"] (Symbol "y")]
 (ESymbol "true") = None.
Proof. vm_compute; reflexivity. Qed.
Example cache_circular_claim : demo_check 8 [Entry 1 "loop" [] (Symbol "true");
 Entry 2 "loop" [] (Symbol "true")] (ECall "loop" []) = None.
Proof. vm_compute; reflexivity. Qed.
Definition typeof_program := {| program_binders := []; program_inputs := [PVar 0];
 program_output := PSymbol "Type";
 program_cases := [{|case_patterns := [PVar 0]; case_body := ETypeof (EVar 0)|}] |}.
Definition typed_check ty := checked_evaluate (closed_nil []) no_extension [] 8
 (fun _=>Some (Symbol ty)) [("typed",typeof_program)]
 [Entry 1 "typed" [Symbol "x"] (Symbol "Int")] [] (ECall "typed" [ESymbol "x"]).
Example cache_query_bound : typed_check "Int"=Some (Symbol "Int").
Proof. vm_compute; reflexivity. Qed.
Example cache_different_query_rejected : typed_check "Bool"=None.
Proof. vm_compute; reflexivity. Qed.
