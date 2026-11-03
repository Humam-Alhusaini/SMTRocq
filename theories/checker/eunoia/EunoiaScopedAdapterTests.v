(**************************************************************************)
(*     SMTCoq -- distributed under the terms of the CeCILL-C licence       *)
(**************************************************************************)
From Stdlib Require Import List String Bool Uint63.
From SMTCoq.utils Require Import PArray CompDec.
From SMTCoq.structures Require Import CompDecInstances.
From SMTCoq.checker.fol Require Import State Terms.
From SMTCoq.checker Require Import MainChecker.
From SMTCoq.checker.eunoia Require Import
  EoSyntax CpcGenerated EunoiaChecker EunoiaAdapter EunoiaLocal EunoiaScope
  EunoiaScopedAdapter.

Import ListNotations.
Local Open Scope uint63_scope.
Local Open Scope array_scope.
Local Open Scope string_scope.

Module EunoiaScopedAdapterTests.
(* Hand-produced LOCAL certificates, not a live solver/importer fixture. Rule
   evaluation is nevertheless the actual signature-generated implementation. *)
Definition sorts : array typ_compdec := PArray.make 1 unit_typ_compdec.
Definition funcs : array (Atom.tval sorts) :=
  (PArray.make 2 (@Atom.Tval sorts ([], Typ.Tbool) true))
    .[1 <- @Atom.Tval sorts ([], Typ.Tbool) false].
Definition atoms : array Atom.atom :=
  (PArray.make 3 (Atom.Acop Atom.CO_xH)).[1 <- Atom.Aapp 0 []].[2 <- Atom.Aapp 1 []].
Definition pair (a b : int) := (PArray.make 2 a).[1 <- b].
Definition forms : array Form.form :=
  (PArray.make 12 Form.Ftrue).[1 <- Form.Ffalse]
    .[2 <- Form.Fatom 1].[3 <- Form.Fatom 2]
    .[4 <- Form.Fimp (pair 4 2)]       (* p => false, literal 8 *)
    .[5 <- Form.Fimp (pair 6 2)]       (* q => false, literal 10 *)
    .[6 <- Form.Fimp (pair 4 10)]      (* p => (q => false), literal 12 *)
    .[7 <- Form.Fand (pair 4 6)]      (* and p q, literal 14 *)
    .[8 <- Form.Fimp (pair 4 4)]      (* p => p, literal 16 *)
    .[9 <- Form.Fiff 4 4]
    .[10 <- Form.For (pair 4 6)]
    .[11 <- Form.Fimp (pair 4 20)].           (* p iff p, literal 18 *)
Definition names := EunoiaAdapter.Naming [] [(0,"p");(1,"q")].
Definition p := Symbol "p".
Definition q := Symbol "q".
Definition f := Symbol "false".
Definition app := EunoiaAdapter.app.
Definition hp := app "=>" [p;f].
Definition hq := app "=>" [q;f].
Definition hpq := app "=>" [p;hq].
Definition pq := app "and" [p;q].
Definition hpp := app "=>" [p;p].
Definition pp := app "=" [p;p].
Definition neg t := app "not" [t].
Definition payload := EunoiaAdapter.Payload.
Definition command := EunoiaLocal.Command.
Definition resolve pos a b c := command (Checker_Ext.Res pos (pair a b)) c.
Definition gate := @EunoiaLocal.gate sorts funcs atoms forms.
Definition eval := @EunoiaScopedAdapter.eval sorts funcs atoms forms names 100.
Definition scope_eval := @EunoiaScopedAdapter.scope_eval sorts funcs atoms forms names 100.
Definition run := @EunoiaScopedAdapter.run sorts funcs atoms forms names 100.
Definition check := @EunoiaScopedAdapter.checker sorts funcs atoms forms names 100 12.
Definition check_b := @EunoiaScopedAdapter.checker_b sorts funcs atoms forms names 100 12.
Definition check_eq := @EunoiaScopedAdapter.checker_eq sorts funcs atoms forms names 100 12.
Definition rho := @EunoiaScopedAdapter.valuation sorts funcs atoms forms.
Definition step := @EunoiaChecker.Step EunoiaAdapter.rule_payload EunoiaLocal.witness.
Definition done : EunoiaScopedAdapter.trace := EunoiaScope.Done.
Definition close := @EunoiaScope.Discharge EunoiaAdapter.rule_payload EunoiaLocal.witness.

Definition contradiction a := EunoiaLocal.Witness 3
  [(0,[a]);(1,[Lit.neg a])] [resolve 2 0 1 []] 2.
Definition copy a := contradiction a.
Definition scope_false a h := EunoiaLocal.Witness 4
  [(0,[Lit.neg a]);(1,[Lit.neg h])]
  [command (Checker_Ext.ImmBuildProj 2 1 0) [a]; resolve 3 0 2 []] 3.
Definition process_false := EunoiaLocal.Witness 6 [(0,[8]);(1,[4])]
  [command (Checker_Ext.ImmBuildDef 2 0) [2;5];
   command (Checker_Ext.CFalse 3) [3]; resolve 4 2 3 [5]; resolve 5 1 4 []] 5.
Definition scope_p := payload "scope" [] [f] hp [8].
Definition process_p := payload "process_scope" [f] [hp] (neg p) [5].
Definition contra_p := payload "contra" [] [p;neg p] f [].
Definition body := EunoiaScope.Next (step 3 [2;1] contra_p [] (contradiction 4)) done.
Definition closing := close 3 4 scope_p [8] (scope_false 4 8).
Definition finish := EunoiaScope.Next (step 5 [4] process_p [5] process_false)
  (EunoiaScope.Next (step 6 [0;5] contra_p [] (contradiction 4)) done).
Definition single : EunoiaScopedAdapter.trace := EunoiaScope.Push 2 4 body (Some closing) finish.
Definition roots : list C.t := [[4];[5]].
Definition root_terms := [p;neg p].
Definition claims : list (clause_id * C.t) := [(0,[4]);(1,[5])].
Definition check_single t goal := check roots root_terms claims t goal.

Example checked_tables : EunoiaAdapter.tables_wf sorts funcs atoms forms names = true.
Proof. vm_compute; reflexivity. Qed.
Example source_scope : scope_eval scope_p 4 [] = Some [8].
Proof. vm_compute; reflexivity. Qed.
Example source_scope_exact_disjunctive_endpoint :
  scope_eval (payload "scope" [] [app "or" [p;q]] (app "=>" [p;app "or" [p;q]]) [22])
    4 [4;6] = Some [22].
Proof. vm_compute; reflexivity. Qed.
Example source_scope_disjunctive_order_rejected :
  scope_eval (payload "scope" [] [app "or" [p;q]] (app "=>" [p;app "or" [p;q]]) [22])
    4 [6;4] = None.
Proof. vm_compute; reflexivity. Qed.
Example source_scope_disjunctive_literal_changed :
  scope_eval (payload "scope" [] [app "or" [p;q]] (app "=>" [p;app "or" [p;q]]) [22])
    4 [4;7] = None.
Proof. vm_compute; reflexivity. Qed.
Example source_process_scope : eval process_p [[8]] = Some [5].
Proof. vm_compute; reflexivity. Qed.
Example scope_semantic_discharge : gate [[5]] [8] (scope_false 4 8) = true.
Proof. vm_compute; reflexivity. Qed.
Example process_semantic_discharge : gate [[8]] [5] process_false = true.
Proof. vm_compute; reflexivity. Qed.
Example checked_single_scope : check_single single 6 = true.
Proof. vm_compute; reflexivity. Qed.
Example single_refutation : ~ Forall (C.valid rho) roots.
Proof. eapply EunoiaScopedAdapter.checker_correct; exact checked_single_scope. Qed.

(* Nested scope exports q=>false to the OUTER scope, then p=>(q=>false)
   to the parent. Ordinary process_scope computes not(and p q). *)
Definition outer_evidence := EunoiaLocal.Witness 6 [(0,[5;10]);(1,[13])]
  [command (Checker_Ext.ImmBuildProj 2 1 0) [4];
   command (Checker_Ext.ImmBuildProj 3 1 1) [11];
   resolve 4 0 2 [10]; resolve 5 4 3 []] 5.
Definition nested_process_evidence := EunoiaLocal.Witness 10 [(0,[12]);(1,[14])]
  [command (Checker_Ext.ImmBuildProj 2 1 0) [4];
   command (Checker_Ext.ImmBuildProj 3 1 1) [6];
   command (Checker_Ext.ImmBuildDef 4 0) [5;10]; resolve 5 2 4 [10];
   command (Checker_Ext.ImmBuildDef 6 5) [2;7];
   command (Checker_Ext.CFalse 7) [3]; resolve 8 6 7 [7]; resolve 9 3 8 []] 9.
Definition contra_q := payload "contra" [] [q;neg q] f [].
Definition nested_body := EunoiaScope.Next (step 4 [3;1] contra_q [] (contradiction 6)) done.
Definition inner_close := close 4 5 (payload "scope" [] [f] hq [10]) [10] (scope_false 6 10).
Definition outer_close := close 5 6 (payload "scope" [] [hq] hpq [12]) [12] outer_evidence.
Definition nested_finish := EunoiaScope.Next
  (step 7 [6] (payload "process_scope" [f] [hpq] (neg pq) [15]) [15] nested_process_evidence)
  (EunoiaScope.Next
    (step 8 [0;7] (payload "contra" [] [pq;neg pq] f []) [] (contradiction 14)) done).
Definition nested : EunoiaScopedAdapter.trace := EunoiaScope.Push 2 4
  (EunoiaScope.Push 3 6 nested_body (Some inner_close) done) (Some outer_close) nested_finish.
Definition nested_roots : list C.t := [[14];[7]].
Definition nested_claims : list (clause_id * C.t) := [(0,[14]);(1,[7])].
Definition check_nested t goal := check nested_roots [pq;neg q] nested_claims t goal.

Example source_nested_scope : scope_eval (payload "scope" [] [hq] hpq [12]) 4 [10] = Some [12].
Proof. vm_compute; reflexivity. Qed.
Example source_nested_process :
  eval (payload "process_scope" [f] [hpq] (neg pq) [15]) [[12]] = Some [15].
Proof. vm_compute; reflexivity. Qed.
Example nested_semantic_discharge : gate [[5;10]] [12] outer_evidence = true.
Proof. vm_compute; reflexivity. Qed.
Example nested_process_semantic_discharge : gate [[12]] [15] nested_process_evidence = true.
Proof. vm_compute; reflexivity. Qed.
Example checked_nested_scopes : check_nested nested 8 = true.
Proof. vm_compute; reflexivity. Qed.
Example nested_refutation : ~ Forall (C.valid rho) nested_roots.
Proof. eapply EunoiaScopedAdapter.checker_correct; exact checked_nested_scopes. Qed.

(* Goal wrappers are exercised with p=>p and p=p. The local certificates
   prove tautologies through existing CNF and resolution checkers. *)
Definition scope_pp_evidence := EunoiaLocal.Witness 5 [(0,[4;5]);(1,[17])]
  [command (Checker_Ext.ImmBuildProj 2 1 0) [4];
   command (Checker_Ext.ImmBuildProj 3 1 1) [5]; resolve 4 2 3 []] 4.
Definition goal_close := close 1 2 (payload "scope" [] [p] hpp [16]) [16] scope_pp_evidence.
Definition goal_prefix rest : EunoiaScopedAdapter.trace := EunoiaScope.Push 1 4 done (Some goal_close)
  (EunoiaScope.Next (step 3 [2] (payload "process_scope" [p] [hpp] hpp [16]) [16] (copy 16)) rest).
Definition goal_trace := goal_prefix (EunoiaScope.Next
  (step 4 [3;0] (payload "contra" [] [hpp;neg hpp] f []) [] (contradiction 16)) done).
Example checked_boolean_goal : check_b 16 true [neg hpp] [(0,[17])] goal_trace 4 = true.
Proof. vm_compute; reflexivity. Qed.
Example boolean_goal_correct : Lit.interp rho 16 = true.
Proof. eapply EunoiaScopedAdapter.checker_b_correct; exact checked_boolean_goal. Qed.
Example checked_negative_boolean_goal : check_b 17 false [neg hpp] [(0,[17])] goal_trace 4 = true.
Proof. vm_compute; reflexivity. Qed.
Example negative_boolean_goal_correct : Lit.interp rho 17 = false.
Proof. eapply EunoiaScopedAdapter.checker_b_correct; exact checked_negative_boolean_goal. Qed.
Definition refl_pp_evidence := EunoiaLocal.Witness 4 [(0,[19])]
  [command (Checker_Ext.ImmBuildDef 1 0) [5];
   command (Checker_Ext.ImmBuildDef2 2 0) [4]; resolve 3 1 2 []] 3.
Definition eq_trace := goal_prefix (EunoiaScope.Next
  (step 4 [] (payload "refl" [p] [] pp [18]) [18] refl_pp_evidence)
  (EunoiaScope.Next (step 5 [4;0] (payload "contra" [] [pp;neg pp] f []) [] (contradiction 18)) done)).
Example checked_equality_goal : check_eq 4 4 19 [neg pp] [(0,[19])] eq_trace 5 = true.
Proof. vm_compute; reflexivity. Qed.
Example equality_goal_correct : Lit.interp rho 4 = Lit.interp rho 4.
Proof. eapply EunoiaScopedAdapter.checker_eq_correct; exact checked_equality_goal. Qed.

Example ordinary_evaluation_preserved : eval = EunoiaAdapter.eval sorts funcs atoms forms names 100.
Proof. reflexivity. Qed.
Example ordinary_scope_rejected : eval scope_p [[]] = None.
Proof. vm_compute; reflexivity. Qed.
Example ordinary_rule_at_pop_rejected : scope_eval process_p 4 [8] = None.
Proof. vm_compute; reflexivity. Qed.
Example changed_pushed_formula : scope_eval scope_p 6 [] = None.
Proof. vm_compute; reflexivity. Qed.
Example changed_pushed_polarity : scope_eval scope_p 5 [] = None.
Proof. vm_compute; reflexivity. Qed.
Example changed_endpoint_clause : scope_eval scope_p 4 [4] = None.
Proof. vm_compute; reflexivity. Qed.
Example guarded_clause_is_not_endpoint : scope_eval scope_p 4 [5] = None.
Proof. vm_compute; reflexivity. Qed.
Example extra_payload_premise : scope_eval (payload "scope" [] [f;p] hp [8]) 4 [] = None.
Proof. vm_compute; reflexivity. Qed.
Example missing_payload_premise : scope_eval (payload "scope" [] [] hp [8]) 4 [] = None.
Proof. vm_compute; reflexivity. Qed.
Example changed_generated_output : scope_eval (payload "scope" [] [f] hq [10]) 4 [] = None.
Proof. vm_compute; reflexivity. Qed.
Example changed_output_clause : scope_eval (payload "scope" [] [f] hp [10]) 4 [] = None.
Proof. vm_compute; reflexivity. Qed.
Example unknown_pop_rule : scope_eval (payload "unsupported" [] [f] hp [8]) 4 [] = None.
Proof. vm_compute; reflexivity. Qed.
Example wrong_endpoint_slot : check_single (EunoiaScope.Push 2 4 body
  (Some (close 2 4 scope_p [8] (scope_false 4 8))) finish) 6 = false.
Proof. vm_compute; reflexivity. Qed.
Example missing_endpoint_slot : check_single (EunoiaScope.Push 2 4 body
  (Some (close 11 4 scope_p [8] (scope_false 4 8))) finish) 6 = false.
Proof. vm_compute; reflexivity. Qed.
Example declared_output_mismatch : check_single (EunoiaScope.Push 2 4 body
  (Some (close 3 4 scope_p [10] (scope_false 4 8))) finish) 6 = false.
Proof. vm_compute; reflexivity. Qed.
Example unguarded_local_premise_leak : check_single (EunoiaScope.Push 2 4 body
  (Some (close 3 4 scope_p [8] (EunoiaLocal.Witness 1 [(0,[])] [] 0))) finish) 6 = false.
Proof. vm_compute; reflexivity. Qed.
Example post_scope_assumption_leak : check_single (EunoiaScope.Push 2 4 body (Some closing)
  (EunoiaScope.Next (step 6 [2;1] contra_p [] (contradiction 4)) done)) 6 = false.
Proof. vm_compute; reflexivity. Qed.
Example post_scope_local_conflict_leak : check_single (EunoiaScope.Push 2 4 body (Some closing) done) 3 = false.
Proof. vm_compute; reflexivity. Qed.
Example post_nested_endpoint_leak : check_nested (EunoiaScope.Push 2 4
  (EunoiaScope.Push 3 6 nested_body (Some inner_close) done) (Some outer_close)
  (EunoiaScope.Next (step 7 [5] (payload "process_scope" [f] [hq] (neg q) [7])
    [7] (scope_false 6 10)) done)) 7 = false.
Proof. vm_compute; reflexivity. Qed.
Example parent_live_set_restored :
  match EunoiaChecker.load_roots 10 (EunoiaChecker.initial 12) nested_roots nested_claims with
  | Some m => match run m (EunoiaScope.Push 2 4
      (EunoiaScope.Push 3 6 nested_body (Some inner_close) done) (Some outer_close) done) with
    | Some next => EunoiaChecker.live next = [6;1;0]
    | None => False end
  | None => False end.
Proof. vm_compute; reflexivity. Qed.
Example unclosed_scope : check_single (EunoiaScope.Push 2 4 body None finish) 6 = false.
Proof. vm_compute; reflexivity. Qed.
Example unclosed_inner_scope : check_nested (EunoiaScope.Push 2 4
  (EunoiaScope.Push 3 6 nested_body None done) (Some outer_close) nested_finish) 8 = false.
Proof. vm_compute; reflexivity. Qed.
Example unclosed_outer_scope : check_nested (EunoiaScope.Push 2 4
  (EunoiaScope.Push 3 6 nested_body (Some inner_close) done) None nested_finish) 8 = false.
Proof. vm_compute; reflexivity. Qed.
Definition unsupported := step 10 [] (payload "unsupported" [] [] p [4]) [4] (copy 4).
Example unused_unsupported_after_global_conflict : check_single (EunoiaScope.Push 2 4 body (Some closing)
  (EunoiaScope.Next (step 5 [4] process_p [5] process_false)
    (EunoiaScope.Next (step 6 [0;5] contra_p [] (contradiction 4))
      (EunoiaScope.Next unsupported done)))) 6 = false.
Proof. vm_compute; reflexivity. Qed.
Example unused_unsupported_after_local_conflict : check_single (EunoiaScope.Push 2 4
  (EunoiaScope.Next (step 3 [2;1] contra_p [] (contradiction 4))
    (EunoiaScope.Next unsupported done)) (Some closing) finish) 6 = false.
Proof. vm_compute; reflexivity. Qed.
Example unused_unsupported_in_inner_scope : check_nested (EunoiaScope.Push 2 4
  (EunoiaScope.Push 3 6 (EunoiaScope.Next unsupported nested_body) (Some inner_close) done)
  (Some outer_close) nested_finish) 8 = false.
Proof. vm_compute; reflexivity. Qed.
Example wrong_authoritative_root_terms : check roots [q;neg p] claims single 6 = false.
Proof. vm_compute; reflexivity. Qed.
Example injected_root_claim : check roots root_terms [(0,[]);(1,[5])] single 6 = false.
Proof. vm_compute; reflexivity. Qed.
Example wrong_boolean_goal : check_b 6 true [neg hpp] [(0,[17])] goal_trace 4 = false.
Proof. vm_compute; reflexivity. Qed.
Example wrong_boolean_polarity : check_b 16 false [neg hpp] [(0,[17])] goal_trace 4 = false.
Proof. vm_compute; reflexivity. Qed.
Example positive_equality_literal : check_eq 4 4 18 [neg pp] [(0,[19])] eq_trace 5 = false.
Proof. vm_compute; reflexivity. Qed.
Example wrong_equality_child : check_eq 4 6 19 [neg pp] [(0,[19])] eq_trace 5 = false.
Proof. vm_compute; reflexivity. Qed.
Example malformed_formula_table :
  @EunoiaScopedAdapter.checker sorts funcs atoms (forms.[1 <- Form.Ftrue]) names
    100 12 roots root_terms claims single 6 = false.
Proof. vm_compute; reflexivity. Qed.
Example malformed_atom_table :
  @EunoiaScopedAdapter.checker sorts funcs (atoms.[1 <- Atom.Aapp 0 [1]]) forms names
    100 12 roots root_terms claims single 6 = false.
Proof. vm_compute; reflexivity. Qed.
Definition bad_atoms := atoms.[1 <- Atom.Aapp 0 [0]].
Example structurally_valid_but_ill_typed :
  Atom.check_atom bad_atoms = true /\ Atom.wt sorts funcs bad_atoms = false.
Proof. vm_compute; split; reflexivity. Qed.
Example runtime_typing_rejects :
  @EunoiaScopedAdapter.checker sorts funcs bad_atoms forms names
    100 12 roots root_terms claims single 6 = false.
Proof. vm_compute; reflexivity. Qed.
Example low_fuel_rejects :
  @EunoiaScopedAdapter.checker sorts funcs atoms forms names
    0 12 roots root_terms claims single 6 = false.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions single_refutation.
Print Assumptions nested_refutation.
Print Assumptions boolean_goal_correct.
Print Assumptions equality_goal_correct.
Print Assumptions negative_boolean_goal_correct.
End EunoiaScopedAdapterTests.
