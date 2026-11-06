(* Component diagnostic. Includes validation, conversion and kernel Qed.
   Collection is outside the timers; this is not a complete tactic benchmark. *)
From Stdlib Require Import List String Bool Arith.
From SMTCoq.checker.eunoia Require Import EoSyntax EoRuntime CpcGenerated
 CpcMemo HelperMemoTests.
Import ListNotations.
Local Open Scope string_scope.
Definition reference n := map (fun t=>derive 500 q "arith_poly_norm" [t] []) (repeat input n).
Definition cached n := match validate_context default_primitive 500 q entries with
 | None=>None
 | Some cache=>Some(map (fun t=>derive_context_cached cache default_primitive 500 q "arith_poly_norm" None [t] []) (repeat input n)) end.
Definition expected n values := match values with
 | None=>false
 | Some xs=>Nat.eqb (List.length xs) n && forallb (fun t=>match t with Some t=>term_eqb t input|_=>false end) xs end.
Goal expected 1000 (Some(reference 1000))=true.
Proof. Time vm_compute. reflexivity. Time Qed.
Goal expected 1000 (cached 1000)=true.
Proof. Time vm_compute. reflexivity. Time Qed.
Goal expected 3000 (Some(reference 3000))=true.
Proof. Time vm_compute. reflexivity. Time Qed.
Goal expected 3000 (cached 3000)=true.
Proof. Time vm_compute. reflexivity. Time Qed.
