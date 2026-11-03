(**************************************************************************)
(*     SMTCoq -- distributed under the terms of the CeCILL-C licence       *)
(**************************************************************************)
From Stdlib Require Import List Bool Uint63.
From SMTCoq.utils Require Import PArray.
From SMTCoq.checker.fol Require Import State Terms.
From SMTCoq.checker Require Import MainChecker.
From SMTCoq.checker.eunoia Require Import EunoiaUf EunoiaLiaTests EunoiaLocal.

Import ListNotations EunoiaLocal.
Local Open Scope uint63_scope.
Local Open Scope array_scope.

Module EunoiaLocalTests.
Definition atoms := Regression.atoms.
Definition forms : array Form.form :=
  (make 14 Form.Ftrue).[1 <- Form.Ffalse]
    .[2 <- Form.Fatom 3].[3 <- Form.Fatom 4].[4 <- Form.Fatom 5]
    .[5 <- Form.Fatom 6].[6 <- Form.Fatom 7]
    .[7 <- Form.Fatom 11].[8 <- Form.Fatom 12]
    .[9 <- Form.Fatom 13].[10 <- Form.Fatom 14]
    .[11 <- Form.Fiff 4 10]       (* (x=y) iff (y=x), literal 22 *)
    .[12 <- Form.Fiff 18 20]      (* P z x iff P z y, literal 24 *)
    .[13 <- Form.For ((make 2 4).[1 <- 6])].

Definition pair (a b : clause_id) : resolution := (make 2 a).[1 <- b].
Definition resolve pos a b c := Command (Checker_Ext.Res pos (pair a b)) c.
Definition trans_program :=
  [Command (Checker_Ext.EqTr 3 8 [4; 6]) [5; 7; 8];
   resolve 4 0 3 [7; 8]; resolve 5 1 4 [8]; resolve 6 2 5 []].
Definition trans_claims : list (clause_id * C.t) := [(0,[4]);(1,[6]);(2,[9])].
Definition trans_witness := Witness 7 trans_claims trans_program 6.

Definition bool_program :=
  [Command (Checker_Ext.BuildDef 3 22) [5;11;22];
   resolve 4 0 3 [11;22]; resolve 5 1 4 [22]; resolve 6 2 5 []].
Definition bool_witness := Witness 7 [(0,[4]);(1,[10]);(2,[23])] bool_program 6.

(* Both directions of predicate congruence plus checked CNF of the negated iff.
   The atom checker alone produces implication clauses, not the unit iff. *)
Definition bool_congr_program :=
  [Command (Checker_Ext.EqTr 2 10 [4]) [5;10];
   resolve 3 0 2 [10];
   Command (Checker_Ext.EqCgrP 4 18 20 [None;Some 4]) [5;19;20];
   resolve 5 0 4 [19;20];
   Command (Checker_Ext.EqCgrP 6 20 18 [None;Some 10]) [11;18;21];
   resolve 7 3 6 [18;21];
   Command (Checker_Ext.ImmBuildDef 8 1) [19;21];
   Command (Checker_Ext.ImmBuildDef2 9 1) [18;20];
   resolve 10 5 8 [19]; resolve 11 7 9 [18]; resolve 12 10 11 []].
Definition bool_congr_witness :=
  Witness 13 [(0,[4]);(1,[25])] bool_congr_program 12.

Section Tables.
Variable t_i : array CompDec.typ_compdec.
Variable t_func : array (Atom.tval t_i).
Local Definition check := @gate t_i t_func atoms forms.

Example checked_tables : Form.check_form forms && Atom.check_atom atoms = true.
Proof. vm_compute; reflexivity. Qed.

Example euf_implication : check [[4];[6]] [8] trans_witness = true.
Proof. vm_compute; reflexivity. Qed.

Example boolean_equality : check [[4];[10]] [22] bool_witness = true.
Proof. vm_compute; reflexivity. Qed.

Example boolean_congruence : check [[4]] [24] bool_congr_witness = true.
Proof. vm_compute; reflexivity. Qed.

Example output_overwrite_rejected : check [[4]] [14]
  (Witness 4 [(0,[4]);(1,[15])]
    [Command (Checker_Ext.EqCgr 2 14 [None;Some 4]) [5;14];
     resolve 3 0 2 [14]; resolve 1 1 3 []] 1) = false.
Proof. vm_compute; reflexivity. Qed.

Example function_congruence_fresh : check [[4]] [14]
  (Witness 5 [(0,[4]);(1,[15])]
    [Command (Checker_Ext.EqCgr 2 14 [None;Some 4]) [5;14];
     resolve 3 0 2 [14]; resolve 4 1 3 []] 4) = true.
Proof. vm_compute; reflexivity. Qed.

Example disjunctive_premise_preserved : check [[4;6]] [4;6]
  (Witness 5 [(0,[4;6]);(1,[5]);(2,[7])]
    [resolve 3 0 1 [6]; resolve 4 2 3 []] 4) = true.
Proof. vm_compute; reflexivity. Qed.

Example formula_disjunction : check [[26]] [4;6]
  (Witness 6 [(0,[26]);(1,[5]);(2,[7])]
    [Command (Checker_Ext.ImmBuildDef 3 0) [4;6];
     resolve 4 3 1 [6]; resolve 5 2 4 []] 5) = true.
Proof. vm_compute; reflexivity. Qed.

Example false_conclusion : check [[4];[5]] []
  (Witness 3 [(0,[4]);(1,[5])] [resolve 2 0 1 []] 2) = true.
Proof. vm_compute; reflexivity. Qed.

Example empty_root_conflict : check [[]] []
  (Witness 1 [(0,[])] [] 0) = true.
Proof. vm_compute; reflexivity. Qed.

Example mutated_endpoint : check [[4];[6]] [10] trans_witness = false.
Proof. vm_compute; reflexivity. Qed.

Example mutated_euf_witness : check [[4];[6]] [8]
  (Witness 7 trans_claims
    (Command (Checker_Ext.EqTr 3 10 [4;6]) [5;7;8] :: tl trans_program) 6) = false.
Proof. vm_compute; reflexivity. Qed.

Example mutated_intermediate_clause : check [[4];[6]] [8]
  (Witness 7 trans_claims
    (Command (Checker_Ext.EqTr 3 8 [4;6]) [8] :: tl trans_program) 6) = false.
Proof. vm_compute; reflexivity. Qed.

Example changed_premise : check [[10];[6]] [8] trans_witness = false.
Proof. vm_compute; reflexivity. Qed.

Example changed_premise_order : check [[6];[4]] [8] trans_witness = false.
Proof. vm_compute; reflexivity. Qed.

Example extra_assumption : check [[4]] [8]
  (Witness 7 trans_claims trans_program 6) = false.
Proof. vm_compute; reflexivity. Qed.

Example dropped_root : check [[4];[6]] [8]
  (Witness 7 [(0,[4]);(2,[9])] trans_program 6) = false.
Proof. vm_compute; reflexivity. Qed.

Example duplicated_root_slot : check [[4];[6]] [8]
  (Witness 7 [(0,[4]);(0,[6]);(2,[9])] trans_program 6) = false.
Proof. vm_compute; reflexivity. Qed.

Example root_out_of_bounds : check [[4];[6]] [8]
  (Witness 7 [(7,[4]);(1,[6]);(2,[9])] trans_program 6) = false.
Proof. vm_compute; reflexivity. Qed.

Example cannot_strengthen_disjunctive_premise : check [[4;6]] [4]
  (Witness 3 [(0,[4;6]);(1,[5])] [resolve 2 0 1 []] 2) = false.
Proof. vm_compute; reflexivity. Qed.

Example cannot_split_disjunctive_root : check [[4;6]] [4]
  (Witness 4 [(0,[4]);(1,[6]);(2,[5])] [resolve 3 0 2 []] 3) = false.
Proof. vm_compute; reflexivity. Qed.

Example global_or_uninitialized_read : check [[4];[6]] [8]
  (Witness 8 trans_claims [resolve 3 0 7 []] 3) = false.
Proof. vm_compute; reflexivity. Qed.

Example forward_read : check [[4];[6]] [8]
  (Witness 7 trans_claims (resolve 4 0 3 [7;8] :: trans_program) 6) = false.
Proof. vm_compute; reflexivity. Qed.

Example read_out_of_bounds : check [[4];[6]] [8]
  (Witness 7 trans_claims [resolve 3 0 7 []] 3) = false.
Proof. vm_compute; reflexivity. Qed.

Example destination_out_of_bounds : check [[4];[6]] [8]
  (Witness 3 trans_claims trans_program 6) = false.
Proof. vm_compute; reflexivity. Qed.

Example empty_resolution : check [[4];[6]] [8]
  (Witness 7 trans_claims [Command (Checker_Ext.Res 3 (make 0 0)) []] 3) = false.
Proof. vm_compute; reflexivity. Qed.

Example long_resolution_rejected : check [[4];[6]] [8]
  (Witness 7 trans_claims [Command (Checker_Ext.Res 3 (make 3 0)) []] 3) = false.
Proof. vm_compute; reflexivity. Qed.

Example unknown_operation_after_conflict : check [[4];[6]] [8]
  (Witness 8 trans_claims
    (trans_program ++ [Command (Checker_Ext.BBVar 7 4) [4]]) 6) = false.
Proof. vm_compute; reflexivity. Qed.

Example dedicated_true_operation : check [[4];[6]] [8]
  (Witness 8 trans_claims
    (Command (Checker_Ext.CTrue 7) C._true :: trans_program) 6) = true.
Proof. vm_compute; reflexivity. Qed.

Example singleton_true_conclusion : check [] C._true
  (Witness 3 [(0, [1])]
    [Command (Checker_Ext.CTrue 1) C._true; resolve 2 0 1 []] 2) = true.
Proof. vm_compute; reflexivity. Qed.

Example euf_fallback_even_with_true_expectation : check [[4];[6]] [8]
  (Witness 8 trans_claims
    (Command (Checker_Ext.EqTr 7 10 [4;6]) C._true :: trans_program) 6) = false.
Proof. vm_compute; reflexivity. Qed.

Example cnf_fallback_rejected : check [[4];[6]] [8]
  (Witness 8 trans_claims
    (Command (Checker_Ext.BuildDef 7 4) C._true :: trans_program) 6) = false.
Proof. vm_compute; reflexivity. Qed.

Example resolution_fallback_rejected : check [[4];[6]] [8]
  (Witness 8 trans_claims
    (resolve 7 0 1 C._true :: trans_program) 6) = false.
Proof. vm_compute; reflexivity. Qed.

Example literal_out_of_bounds : check [[4];[6]] [8]
  (Witness 8 trans_claims
    (Command (Checker_Ext.EqTr 7 198 []) C._true :: trans_program) 6) = false.
Proof. vm_compute; reflexivity. Qed.

Example noncanonical_root : check [[6;4]] [4;6]
  (Witness 5 [(0,[6;4]);(1,[5]);(2,[7])]
    [resolve 3 0 1 [6]; resolve 4 2 3 []] 4) = false.
Proof. vm_compute; reflexivity. Qed.

Example noncanonical_conclusion : check [[4;6]] [6;4]
  (Witness 5 [(0,[4;6]);(1,[7]);(2,[5])]
    [resolve 3 0 1 [4]; resolve 4 2 3 []] 4) = false.
Proof. vm_compute; reflexivity. Qed.

Example malformed_premise_literal : check [[198]] []
  (Witness 1 [(0,[198])] [] 0) = false.
Proof. vm_compute; reflexivity. Qed.

Example malformed_conclusion_literal : check [[4]] [198]
  (Witness 2 [(0,[4]);(1,[199])] [] 0) = false.
Proof. vm_compute; reflexivity. Qed.

Example duplicate_command_rejected : check [[4];[6]] [8]
  (Witness 7 trans_claims
    (hd (Command (Checker_Ext.CTrue 3) []) trans_program :: trans_program) 6) = false.
Proof. vm_compute; reflexivity. Qed.

Example unsupported_invalid_form_table :
  @gate t_i t_func atoms (make 14 Form.Ftrue) [[4]] [4]
    (Witness 3 [(0,[4]);(1,[5])] [resolve 2 0 1 []] 2) = false.
Proof. vm_compute; reflexivity. Qed.

Example unsupported_invalid_atom_table :
  @gate t_i t_func (make 1 (Atom.Aapp 0 [])) forms [[4]] [4]
    (Witness 3 [(0,[4]);(1,[5])] [resolve 2 0 1 []] 2) = false.
Proof. vm_compute; reflexivity. Qed.

Example conflict_out_of_bounds : check [[4];[6]] [8]
  (Witness 7 trans_claims trans_program 7) = false.
Proof. vm_compute; reflexivity. Qed.

Example conflict_uninitialized : check [[4];[6]] [8]
  (Witness 8 trans_claims trans_program 7) = false.
Proof. vm_compute; reflexivity. Qed.

Example wrong_conflict : check [[4];[6]] [8]
  (Witness 7 trans_claims trans_program 5) = false.
Proof. vm_compute; reflexivity. Qed.

(* A local LIA lemma followed by two resolution operations. *)
Example lia_composition : @gate t_i t_func EunoiaLiaTests.atoms EunoiaLiaTests.forms
  [[4]] [6]
  (Witness 5 [(0,[4]);(1,[7])]
    [Command (Checker_Ext.LiaMicromega 2 [5;6] []) [5;6];
     resolve 3 0 2 [6]; resolve 4 1 3 []] 4) = true.
Proof. vm_compute; reflexivity. Qed.
End Tables.
End EunoiaLocalTests.
