(**************************************************************************)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2026                                          *)
(*     Distributed under the terms of the CeCILL-C licence (see LICENSE). *)
(**************************************************************************)

From Stdlib Require Import List Bool Uint63 BinPos.
From SMTCoq.utils Require Import PArray.
From SMTCoq.checker.fol Require Import State Terms.
From SMTCoq.checker Require Import MainChecker.
From SMTCoq.checker.eunoia Require Import EunoiaChecker EunoiaBridge EunoiaScope.

Import ListNotations EunoiaChecker.
Local Open Scope uint63_scope.
Local Open Scope array_scope.

Module EunoiaScopeTests.

(* These deliberately untrusted evaluators test the scope mechanism, not CPC
   coverage. Both ordinary and scope results must pass the REAL bridge gate. *)
Inductive rule := Return (c : C.t) | Unknown.
Definition eval (r : rule) (_ : list C.t) : option C.t :=
  match r with Return c => Some c | Unknown => None end.
Inductive scope_rule := Export (a : _lit) (local result : C.t) | UnknownScope.
Definition scope_eval (r : scope_rule) (a : _lit) (c : C.t) : option C.t :=
  match r with
  | Export expected local result =>
    if (expected =? a) && clause_eqb local c then Some result else None
  | UnknownScope => None
  end.

Definition trace := @EunoiaScope.trace rule scope_rule EunoiaBridge.witness.
Definition done : trace := EunoiaScope.Done.
Definition resolution2 := (PArray.make 2 0).[1 <- 1].
Definition res2 := EunoiaBridge.Witness 3 (Checker_Ext.Res 2 resolution2).
Definition weaken (c : C.t) := EunoiaBridge.Witness 2 (Checker_Ext.Weaken 1 0 c).
Definition resolve (dst : clause_id) (ids : list clause_id) :=
  Step dst ids (Return []) [] res2.

Definition forms : array Form.form := (PArray.make 5 Form.Ftrue).[1 <- Form.Ffalse].
Definition roots : list C.t := [[4]; [5]; [6]; [8]].
Definition claims : list (clause_id * C.t) :=
  [(0, [4]); (1, [5]); (2, [6]); (3, [8])].
Definition inner := EunoiaScope.Discharge 6 7 (Export 8 [] [9]) [9] (weaken [9]).
Definition outer := EunoiaScope.Discharge 7 8 (Export 6 [9] [7;9])
  [7;9] (weaken [7;9]).
Definition body : trace := EunoiaScope.Next (resolve 6 [0;1]) done.
Definition inner_trace : trace := EunoiaScope.Push 5 8 body (Some inner) done.
(* Every resolution link has its own fresh result and checked expectation. *)
Definition finish_with (tail : trace) : trace :=
  EunoiaScope.Next (Step 10 [8;2] (Return [9]) [9] res2)
    (EunoiaScope.Next (resolve 9 [10;3]) tail).
Definition finish : trace := finish_with done.
Definition nested : trace := EunoiaScope.Push 4 6 inner_trace (Some outer) finish.

Section Context.
  Variable t_i : array CompDec.typ_compdec.
  Variable t_func : array (Atom.tval t_i).
  Variable t_atom : array Atom.atom.
  Local Definition gate := @EunoiaBridge.gate t_i t_func t_atom forms.
  Local Definition check := EunoiaScope.checker eval scope_eval gate 5 12 roots claims.
  Local Definition run := EunoiaScope.run eval scope_eval gate 5.

  Example nested_scopes_accept : check nested 9 = true.
  Proof. vm_compute; reflexivity. Qed.

  (* The final resolution really needs the outer exported clause. *)
  Example omitted_scopes_rejected : check finish 9 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example wrong_discharge_endpoint_rejected :
    check (EunoiaScope.Push 4 6 inner_trace
      (Some (EunoiaScope.Discharge 5 8 (Export 6 [9] [7;9])
        [7;9] (weaken [7;9]))) finish) 9 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example different_live_endpoint_rejected_by_evaluator :
    check (EunoiaScope.Push 4 6 inner_trace
      (Some (EunoiaScope.Discharge 0 8 (Export 6 [9] [7;9])
        [7;9] (weaken [7;9]))) finish) 9 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example wrong_assumption_rejected :
    check (EunoiaScope.Push 4 4 inner_trace (Some outer) finish) 9 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example unknown_pop_rejected :
    check (EunoiaScope.Push 4 6 inner_trace
      (Some (EunoiaScope.Discharge 7 8 UnknownScope [7;9] (weaken [7;9])))
      finish) 9 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example pop_generated_result_mismatch_rejected :
    check (EunoiaScope.Push 4 6 inner_trace
      (Some (EunoiaScope.Discharge 7 8 (Export 6 [9] [7;9]) [] res2))
      finish) 9 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example pop_semantic_result_mismatch_rejected :
    check (EunoiaScope.Push 4 6 inner_trace
      (Some (EunoiaScope.Discharge 7 8 (Export 6 [9] []) [] (weaken [7;9])))
      finish) 9 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example pop_cannot_export_unguarded_local_result :
    check (EunoiaScope.Push 4 6 inner_trace
      (Some (EunoiaScope.Discharge 7 8 (Export 6 [9] [9]) [9] (weaken [9])))
      finish) 9 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example inner_local_result_expires_before_outer_pop :
    check (EunoiaScope.Push 4 6 inner_trace
      (Some (EunoiaScope.Discharge 6 8 (Export 6 [] [7]) [7] (weaken [7])))
      finish) 9 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example outer_local_result_expires :
    check (EunoiaScope.Push 4 6 inner_trace (Some outer)
      (EunoiaScope.Next (resolve 11 [7;3]) finish)) 9 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example pushed_assumption_expires :
    check (EunoiaScope.Push 4 6 inner_trace (Some outer)
      (EunoiaScope.Next (Step 11 [4;8] (Return [9]) [9] res2) finish)) 9 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example local_conflict_is_not_global :
    check (EunoiaScope.Push 4 6 inner_trace (Some outer) done) 6 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example branch_local_goal_rejected : check nested 7 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example wrong_goal_rejected : check nested 8 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example changed_root_rejected :
    EunoiaScope.checker eval scope_eval gate 5 12 roots
      [(0,[4]);(1,[4]);(2,[6]);(3,[8])] nested 9 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example unknown_unused_local_step_rejected :
    check (EunoiaScope.Push 4 6
      (EunoiaScope.Next (Step 10 [] Unknown [0]
        (EunoiaBridge.Witness 1 (Checker_Ext.CTrue 0))) inner_trace)
      (Some outer) finish) 9 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example unknown_after_local_conflict_rejected :
    check (EunoiaScope.Push 4 6
      (EunoiaScope.Push 5 8
        (EunoiaScope.Next (resolve 6 [0;1])
          (EunoiaScope.Next (Step 10 [] Unknown [] res2) done))
        (Some inner) done) (Some outer) finish) 9 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example unknown_after_global_conflict_rejected :
    check (EunoiaScope.Push 4 6 inner_trace (Some outer)
      (finish_with (EunoiaScope.Next (Step 11 [] Unknown [] res2) done))) 9 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example unclosed_scope_rejected :
    check (EunoiaScope.Push 4 6 inner_trace None finish) 9 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example unclosed_nested_scope_rejected :
    check (EunoiaScope.Push 4 6 (EunoiaScope.Push 5 8 body None done)
      (Some outer) finish) 9 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example pop_cannot_overwrite_parent :
    check (EunoiaScope.Push 4 6 inner_trace
      (Some (EunoiaScope.Discharge 7 0 (Export 6 [9] [7;9])
        [7;9] (weaken [7;9]))) finish) 9 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example duplicate_push_slot_rejected :
    check (EunoiaScope.Push 0 6 inner_trace (Some outer) finish) 9 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example malformed_assumption_rejected :
    check (EunoiaScope.Push 4 10 inner_trace (Some outer) finish) 9 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example out_of_bounds_push_rejected :
    check (EunoiaScope.Push 12 6 inner_trace (Some outer) finish) 9 = false.
  Proof. vm_compute; reflexivity. Qed.

  (* Here [5] is actually false: forms.[2] = Ftrue. An inconsistent local
     context may prove [], but the parent receives only the valid guard [4]. *)
  Definition false_assumption_trace : trace := EunoiaScope.Push 1 5
    (EunoiaScope.Next (resolve 2 [0;1]) done)
    (Some (EunoiaScope.Discharge 2 3 (Export 5 [] [4]) [4] (weaken [4]))) done.
  Definition single_root := load_roots 5 (initial 4) [[4]] [(0,[4])].

  Example false_local_assumption_discharged :
    match single_root with
    | Some m => match run m false_assumption_trace with
                | Some next => available next 3 &&
                    clause_eqb (S.get (clauses next) 3) [4] &&
                    negb (available next 1) && negb (available next 2)
                | None => false end
    | None => false end = true.
  Proof. vm_compute; reflexivity. Qed.

  Example false_local_assumption_cannot_refute_parent :
    EunoiaScope.checker eval scope_eval gate 5 4 [[4]] [(0,[4])]
      false_assumption_trace 2 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example false_local_assumption_cannot_export_false :
    EunoiaScope.checker eval scope_eval gate 5 4 [[4]] [(0,[4])]
      (EunoiaScope.Push 1 5 (EunoiaScope.Next (resolve 2 [0;1]) done)
        (Some (EunoiaScope.Discharge 2 3 (Export 5 [] []) [] (weaken []))) done)
      3 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example local_assumption_really_false :
    Lit.interp (@EunoiaBridge.valuation t_i t_func t_atom forms) 5 = false.
  Proof. vm_compute; reflexivity. Qed.
End Context.

(* Fully concrete tables exercise the runtime typing guard and the goal wrapper. *)
Definition types : array CompDec.typ_compdec := PArray.make 0 CompDecInstances.unit_typ_compdec.
Definition funcs : array (Atom.tval types) :=
  PArray.make 0 (Atom.Tval types ([], Typ.Tpositive) 1%positive).
Definition atoms : array Atom.atom := PArray.make 0 (Atom.Acop Atom.CO_xH).
Definition ill_typed_atoms : array Atom.atom :=
  (PArray.make 2 (Atom.Acop Atom.CO_xH)).[1 <- Atom.Auop Atom.UO_Zopp 0].
Definition truth_proof : trace :=
  EunoiaScope.Next (Step 1 [] (Return [0]) [0]
    (EunoiaBridge.Witness 1 (Checker_Ext.CTrue 0)))
    (EunoiaScope.Next (resolve 2 [0;1]) done).

Example goal_wrapper_accepts :
  @EunoiaScope.checker_b types funcs atoms forms rule scope_rule eval scope_eval
    0 true 3 [(0,[1])] truth_proof 2 = true.
Proof. vm_compute; reflexivity. Qed.

Example goal_wrapper_binds_negated_goal :
  @EunoiaScope.checker_b types funcs atoms forms rule scope_rule eval scope_eval
    2 true 3 [(0,[1])] truth_proof 2 = false.
Proof. vm_compute; reflexivity. Qed.

Example goal_wrapper_binds_polarity :
  @EunoiaScope.checker_b types funcs atoms forms rule scope_rule eval scope_eval
    0 false 3 [(0,[1])] truth_proof 2 = false.
Proof. vm_compute; reflexivity. Qed.

Example malformed_formula_table_rejected :
  @EunoiaScope.table_checker types funcs atoms (PArray.make 5 Form.Ftrue)
    rule scope_rule eval scope_eval 3 [[1]] [(0,[1])] truth_proof 2 = false.
Proof. vm_compute; reflexivity. Qed.

Example malformed_atom_table_rejected :
  @EunoiaScope.table_checker types funcs (PArray.make 0 (Atom.Acop Atom.CO_Z0))
    forms rule scope_rule eval scope_eval 3 [[1]] [(0,[1])] truth_proof 2 = false.
Proof. vm_compute; reflexivity. Qed.

Example ill_typed_table_is_structurally_wellformed :
  Atom.check_atom ill_typed_atoms = true.
Proof. vm_compute; reflexivity. Qed.

Example ill_typed_atom_table_rejected :
  @EunoiaScope.table_checker types funcs ill_typed_atoms forms
    rule scope_rule eval scope_eval 3 [[1]] [(0,[1])] truth_proof 2 = false.
Proof. vm_compute; reflexivity. Qed.

End EunoiaScopeTests.
