(* SMTCoq -- distributed under the CeCILL-C licence (see LICENSE). *)
From Stdlib Require Import List String Bool Uint63.
From SMTCoq.utils Require Import PArray.
From SMTCoq.checker.fol Require Import State Terms.
From SMTCoq.checker.eunoia Require Import EunoiaAdapter EunoiaChecker EunoiaScope
 EunoiaMemo EunoiaMemoTests EunoiaModelDag EunoiaModelDagCheck.
Import ListNotations.
Local Open Scope uint63_scope.
Local Open Scope string_scope.
Local Open Scope array_scope.
Module T := EunoiaMemoTests.
Module S := T.S.
Module D := EunoiaModelDagCheck.
Definition check fuel cache roots root_terms t :=
 @D.checker S.sorts S.funcs S.atoms S.forms S.names
 fuel cache 12 roots root_terms S.claims t 6.
Example shared_scoped_source_accepts :
 check 100 T.entries S.roots S.root_terms T.shared = true.
Proof. vm_compute; reflexivity. Qed.
Example inline_source_accepts :
 check 100 [] S.roots S.root_terms (T.inline_trace S.single) = true.
Proof. vm_compute; reflexivity. Qed.
Example wrong_root_order_rejected :
 check 100 T.entries S.roots (rev S.root_terms) T.shared = false.
Proof. vm_compute; reflexivity. Qed.
Example unused_bad_semantics_rejected :
 check 100 (T.entries ++ [T.invalid]) S.roots S.root_terms T.shared = false.
Proof. vm_compute; reflexivity. Qed.
Definition unsupported := EunoiaAdapter.Payload "unsupported" [] [S.p; S.neg S.p] S.f [].
Example bad_source_after_conflict_rejected :
 check 100 T.entries S.roots S.root_terms
 (EunoiaScope.Push 2 4 T.body (Some T.closing)
  (EunoiaScope.Next (T.step 5 [4] S.process_p [5] (EunoiaMemo.Cached 2))
   (EunoiaScope.Next (T.step 6 [0;5] S.contra_p [] (EunoiaMemo.Cached 0))
    (EunoiaScope.Next (T.step 7 [0;5] unsupported [] (EunoiaMemo.Cached 0)) T.done)))) = false.
Proof. vm_compute; reflexivity. Qed.
Example bad_inline_semantics_rejected :
 check 100 T.entries S.roots S.root_terms
 (EunoiaScope.Push 2 4
  (EunoiaScope.Next (T.step 3 [2;1] S.contra_p []
    (EunoiaMemo.Inline (T.invalid.(EunoiaMemo.cached_witness)))) T.done)
  (Some T.closing) T.finish) = false.
Proof. vm_compute; reflexivity. Qed.
Example low_fuel_retains_failure :
 check 0 T.entries S.roots S.root_terms T.shared = false.
Proof. vm_compute; reflexivity. Qed.
Example indexed_model_low_fuel :
 EunoiaModelDag.encoding_entries S.sorts S.funcs S.atoms S.forms S.names 0 [4;5;8] =
 [(4,None);(5,None);(8,None)].
Proof. vm_compute; reflexivity. Qed.
Example indexed_model_out_of_bounds :
 EunoiaModelDag.encoding_entries S.sorts S.funcs S.atoms S.forms S.names 100 [1000] =
 [(1000,None)].
Proof. vm_compute; reflexivity. Qed.
(* Fnot2 deliberately uses the original encoder. Its descendants must still
   encode correctly when the single pass cannot cache their prerequisite. *)
Definition fallback_forms := S.forms.[8 <- Form.Fnot2 1 4].
Example unsupported_cache_node_falls_back :
 EunoiaModelDag.encoding_entries S.sorts S.funcs S.atoms fallback_forms S.names 100 [16] =
 EunoiaAdapter.encoding_entries S.sorts S.funcs S.atoms fallback_forms S.names 100 [16].
Proof. vm_compute; reflexivity. Qed.
Example acceptance_is_original_acceptance :
 check 100 T.entries S.roots S.root_terms T.shared = T.check T.entries T.shared.
Proof. apply D.checker_refinement. Qed.
Print Assumptions acceptance_is_original_acceptance.
