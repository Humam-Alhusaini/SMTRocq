(* SMTCoq -- distributed under the CeCILL-C licence (see LICENSE). *)
From Stdlib Require Import List String Bool Arith Uint63.
From SMTCoq.checker.fol Require Import State Terms.
From SMTCoq.checker.eunoia Require Import EoSyntax EoRuntime CpcGenerated
 EoCheckedMemo CpcMemo CpcMemoCollector EunoiaAdapter EunoiaChecker EunoiaMemo
 EunoiaScope EunoiaMemoTests EunoiaHelperCache.
Import ListNotations.
Local Open Scope uint63_scope.
Local Open Scope string_scope.
Module H := EunoiaHelperCache.
Module T := EunoiaMemoTests.
Definition query := EunoiaAdapter.typeof_with_ready T.S.sorts T.S.funcs T.S.names
 (EunoiaAdapter.names_wf T.S.sorts T.S.funcs T.S.names) 100.
Definition helpers := Eval vm_compute in collect_context default_primitive 100 query
 "process_scope" None [T.S.f] [T.S.hp].
Definition check hints t := @H.checker T.S.sorts T.S.funcs T.S.atoms T.S.forms T.S.names
 100 hints T.entries 12 T.S.roots T.S.root_terms T.S.claims t 6.
Example collected_helpers_nonempty : Nat.ltb 0 (List.length helpers)=true.
Proof. vm_compute; reflexivity. Qed.
Example helper_shared_scoped_refutation : check helpers T.shared=true.
Proof. vm_compute; reflexivity. Qed.
Definition corrupt e := EoCheckedMemo.Entry (EoCheckedMemo.entry_depth e)
 (EoCheckedMemo.entry_name e) (EoCheckedMemo.entry_args e) (Symbol "forged").
Example wrong_helper_value_rejects : check (map corrupt helpers) T.shared=false.
Proof. vm_compute; reflexivity. Qed.
Definition unknown := EoCheckedMemo.Entry 1 "unknown" [] (Symbol "false").
Example unused_unknown_helper_rejects : check (helpers ++ [unknown]) T.shared=false.
Proof. vm_compute; reflexivity. Qed.
Example source_rules_remain_checked :
 check helpers (EunoiaScope.Push 2 4
  (EunoiaScope.Next (T.step 3 [2;1]
   (EunoiaAdapter.Payload "unsupported" [] [T.S.p; T.S.neg T.S.p] T.S.f []) [] (T.M.Cached 0)) T.done)
  (Some T.closing) T.finish)=false.
Proof. vm_compute; reflexivity. Qed.
Example helper_refutation_is_sound : ~ Forall (C.valid T.S.rho) T.S.roots.
Proof. eapply H.checker_correct; exact helper_shared_scoped_refutation. Qed.
Print Assumptions helper_refutation_is_sound.
