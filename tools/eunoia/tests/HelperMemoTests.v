From Stdlib Require Import List String Bool Arith.
From SMTCoq.checker.eunoia Require Import EoSyntax EoRuntime CpcGenerated
 EoCheckedMemo CpcMemo CpcMemoCollector LiaTraceReplay.
Import ListNotations EoCheckedMemo.
Local Open Scope string_scope.
Definition q := lia_query [("x",Symbol "Int")].
Definition b op a c := Apply (Apply (Symbol op) a) c.
Definition input := b "=" (b "+" (Symbol "x") (Symbol "0")) (Symbol "x").
Definition entries := Eval vm_compute in collect_context default_primitive 500 q "arith_poly_norm" None [input] [].
Definition run hints := derive_checked hints default_primitive 500 q "arith_poly_norm" None [input] [].
Example source_cache_nonempty : Nat.ltb 0 (List.length entries)=true.
Proof. vm_compute; reflexivity. Qed.
Example source_cache_valid : run entries=Some input.
Proof. vm_compute; reflexivity. Qed.
Example source_reference : derive 500 q "arith_poly_norm" [input] []=Some input.
Proof. vm_compute; reflexivity. Qed.
Definition corrupt_value e := Entry (entry_depth e) (entry_name e) (entry_args e) (Symbol "forged").
Definition corrupt_args e := Entry (entry_depth e) (entry_name e) [Symbol "unknown"] (entry_value e).
Definition corrupt_name e := Entry (entry_depth e) "unknown" (entry_args e) (entry_value e).
Example source_cache_wrong_value : run (map corrupt_value entries)=None.
Proof. vm_compute; reflexivity. Qed.
Example source_cache_wrong_args : run (map corrupt_args entries)=None.
Proof. vm_compute; reflexivity. Qed.
Example source_cache_wrong_name : run (map corrupt_name entries)=None.
Proof. vm_compute; reflexivity. Qed.
Example source_cache_unused_corruption : derive_checked (map corrupt_name entries) default_primitive 500 q "refl" None [Symbol "x"] []=None.
Proof. vm_compute; reflexivity. Qed.
Example source_cache_cannot_bypass_requires :
 derive_checked entries default_primitive 500 q "arith_poly_norm" None
 [b "=" (b "+" (Symbol "x") (Symbol "1")) (Symbol "x")] []=None.
Proof. vm_compute; reflexivity. Qed.
Example source_cache_cannot_bypass_premises :
 derive_checked entries default_primitive 500 q "arith_poly_norm" None [input] [Symbol "true"]=None.
Proof. vm_compute; reflexivity. Qed.
Example source_cache_cannot_bypass_assumption :
 derive_checked entries default_primitive 500 q "arith_poly_norm" (Some (Symbol "true")) [input] []=None.
Proof. vm_compute; reflexivity. Qed.
Example source_cache_cannot_bypass_fuel :
 derive_checked entries default_primitive 0 q "arith_poly_norm" None [input] []=None.
Proof. vm_compute; reflexivity. Qed.
Print Assumptions derive_checked_correct.
