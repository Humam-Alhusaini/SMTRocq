(**************************************************************************)
(* SMTCoq -- distributed under the terms of the CeCILL-C licence            *)
(**************************************************************************)
From Stdlib Require Import Bool List Uint63 ZArith.
From SMTCoq.utils Require Import PArray CompDec.
From SMTCoq.checker.fol Require Import State Terms.
From SMTCoq.checker.small_checker.euf Require Import EUF.
From SMTCoq.checker.eunoia Require Import EunoiaBool.

Import ListNotations EunoiaBool.
Local Open Scope uint63_scope.
Local Open Scope array_scope.

Module EunoiaBoolTests.
Section TypedTables.
  Variables (a b : bool) (f g : bool -> bool) (h : bool -> Z)
            (x y : Z) (k : bool -> Z -> Z) (p : Z -> bool).
  Variable t_i : array typ_compdec.

  Definition funcs : array (Atom.tval t_i) :=
    (make 9 (@Atom.Tval t_i ([], Typ.Tbool) true))
      .[0 <- @Atom.Tval t_i ([], Typ.Tbool) a]
      .[1 <- @Atom.Tval t_i ([], Typ.Tbool) b]
      .[2 <- @Atom.Tval t_i ([Typ.Tbool], Typ.Tbool) f]
      .[3 <- @Atom.Tval t_i ([Typ.Tbool], Typ.Tbool) g]
      .[4 <- @Atom.Tval t_i ([Typ.Tbool], Typ.TZ) h]
      .[5 <- @Atom.Tval t_i ([], Typ.TZ) x]
      .[6 <- @Atom.Tval t_i ([], Typ.TZ) y]
      .[7 <- @Atom.Tval t_i ([Typ.Tbool; Typ.TZ], Typ.TZ) k]
      .[8 <- @Atom.Tval t_i ([Typ.TZ], Typ.Tbool) p].

  Definition atoms : array Atom.atom :=
    (make 23 (Atom.Acop Atom.CO_xH))
      .[1 <- Atom.Aapp 0 []].[2 <- Atom.Aapp 1 []]
      .[3 <- Atom.Aapp 2 [1]].[4 <- Atom.Aapp 2 [2]]
      .[5 <- Atom.Aapp 3 [1]]
      .[6 <- Atom.Aapp 4 [1]].[7 <- Atom.Aapp 4 [2]]
      .[8 <- Atom.Abop (Atom.BO_eq Typ.TZ) 6 7]
      .[9 <- Atom.Aapp 5 []].[10 <- Atom.Aapp 6 []]
      .[11 <- Atom.Abop (Atom.BO_eq Typ.TZ) 9 10]
      .[12 <- Atom.Aapp 7 [1;9]].[13 <- Atom.Aapp 7 [2;10]]
      .[14 <- Atom.Abop (Atom.BO_eq Typ.TZ) 12 13]
      .[15 <- Atom.Abop (Atom.BO_eq Typ.Tbool) 1 2]
      .[16 <- Atom.Abop (Atom.BO_eq Typ.TZ) 1 2]
      .[17 <- Atom.Aapp 2 [1]]
      .[19 <- Atom.Aapp 99 [1]].[20 <- Atom.Aapp 99 [2]]
      .[21 <- Atom.Aapp 8 [9]].[22 <- Atom.Aapp 8 [10]].

  Definition forms : array Form.form :=
    (make 33 Form.Ftrue).[1 <- Form.Ffalse]
      .[2 <- Form.Fatom 1].[3 <- Form.Fatom 2]
      .[4 <- Form.Fiff 4 6]
      .[5 <- Form.Fatom 3].[6 <- Form.Fatom 4]
      .[7 <- Form.Fiff 10 12]
      .[8 <- Form.Fiff 6 4]
      .[9 <- Form.Fatom 5].[10 <- Form.Fiff 10 18]
      .[11 <- Form.Fatom 8]
      .[12 <- Form.Fatom 9].[13 <- Form.Fatom 10]
      .[14 <- Form.Fiff 24 26]
      .[15 <- Form.Fatom 11].[16 <- Form.Fatom 14]
      .[17 <- Form.Fatom 15].[18 <- Form.Fatom 16]
      .[19 <- Form.Fiff 5 6].[20 <- Form.Fiff 4 7]
      .[21 <- Form.Fiff 0 2]
      .[22 <- Form.Fatom 99].[23 <- Form.Fiff 44 6]
      .[24 <- Form.Fiff 198 6]
      .[25 <- Form.Fatom 19].[26 <- Form.Fatom 20]
      .[27 <- Form.Fiff 50 52]
      .[28 <- Form.Fatom 17].[29 <- Form.Fiff 10 56]
      .[30 <- Form.Fatom 21].[31 <- Form.Fatom 22]
      .[32 <- Form.Fiff 60 62].

  Local Definition check := check_congr t_i funcs atoms forms.
  Local Definition view := equality_view t_i funcs atoms forms.

  Example atom_table_checked : Atom.check_atom atoms = true.
  Proof. vm_compute; reflexivity. Qed.
  (* Deliberately malformed form 24 is excluded from the semantic test below. *)
  Definition checked_forms := forms.[24 <- Form.Ftrue].
  Definition checked_atoms := atoms.[16 <- Atom.Acop Atom.CO_xH]
    .[19 <- Atom.Acop Atom.CO_xH].[20 <- Atom.Acop Atom.CO_xH].
  Example typed_atom_table : Atom.wt t_i funcs checked_atoms = true.
  Proof. vm_compute; reflexivity. Qed.
  Example checked_atom_table : Atom.check_atom checked_atoms = true.
  Proof. vm_compute; reflexivity. Qed.
  Example form_table_checked : Form.check_form checked_forms = true.
  Proof. vm_compute; reflexivity. Qed.

  Example boolean_congruence : check 14 [Some 8] [14;9] = true.
  Proof. vm_compute; reflexivity. Qed.
  Example old_euf_cannot_use_iff :
    EUF.check_congr forms atoms 22 [Some 8] = C._true.
  Proof. vm_compute; reflexivity. Qed.
  Example boolean_argument_integer_result : check 22 [Some 8] [22;9] = true.
  Proof. vm_compute; reflexivity. Qed.
  Example mixed_argument_types : check 32 [Some 8;Some 30] [32;9;31] = true.
  Proof. vm_compute; reflexivity. Qed.
  Example integer_argument_boolean_result : check 64 [Some 30] [64;31] = true.
  Proof. vm_compute; reflexivity. Qed.
  Example ordinary_boolean_atom_equality : check 14 [Some 34] [14;35] = true.
  Proof. vm_compute; reflexivity. Qed.
  Example reverse_endpoints : check 14 [Some 16] [14;17] = true.
  Proof. vm_compute; reflexivity. Qed.
  Example unchanged_argument : check 58 [None] [58] = true.
  Proof. vm_compute; reflexivity. Qed.

  Example nonboolean_projection_rejected : view 28 = None.
  Proof. vm_compute; reflexivity. Qed.
  Example mistyped_atomic_equality_rejected : view 36 = None.
  Proof. vm_compute; reflexivity. Qed.
  Example negative_premise_rejected : check 14 [Some 9] [14;8] = false.
  Proof. vm_compute; reflexivity. Qed.
  Example negative_conclusion_rejected : check 15 [Some 8] [15;9] = false.
  Proof. vm_compute; reflexivity. Qed.
  Example negative_left_operand_rejected : view 38 = None.
  Proof. vm_compute; reflexivity. Qed.
  Example negative_right_operand_rejected : view 40 = None.
  Proof. vm_compute; reflexivity. Qed.
  Example formula_constant_operand_rejected : view 42 = None.
  Proof. vm_compute; reflexivity. Qed.
  Example formula_oob_rejected : view 198 = None.
  Proof. vm_compute; reflexivity. Qed.
  Example equality_atom_oob_rejected : view 44 = None.
  Proof. vm_compute; reflexivity. Qed.
  Example operand_atom_oob_rejected : view 46 = None.
  Proof. vm_compute; reflexivity. Qed.
  Example operand_formula_oob_rejected : view 48 = None.
  Proof. vm_compute; reflexivity. Qed.
  Example equality_endpoint_oob_rejected :
    equality_view t_i funcs
      atoms.[8 <- Atom.Abop (Atom.BO_eq Typ.TZ) 6 99] forms 22 = None.
  Proof. vm_compute; reflexivity. Qed.
  Example one_nonboolean_operand_rejected :
    equality_view t_i funcs atoms forms.[14 <- Form.Fiff 4 26] 28 = None.
  Proof. vm_compute; reflexivity. Qed.
  Example both_negated_operands_rejected :
    equality_view t_i funcs atoms forms.[4 <- Form.Fiff 5 7] 8 = None.
  Proof. vm_compute; reflexivity. Qed.
  Example nonequality_atom_rejected : view 4 = None.
  Proof. vm_compute; reflexivity. Qed.
  Example nonapplication_congruence_rejected : check 30 [] [30] = false.
  Proof. vm_compute; reflexivity. Qed.
  Example function_oob_rejected : check 54 [Some 8] [54;9] = false.
  Proof. vm_compute; reflexivity. Qed.
  Example different_function_rejected : check 20 [Some 8] [20;9] = false.
  Proof. vm_compute; reflexivity. Qed.
  Example missing_equality_rejected : check 14 [None] [14] = false.
  Proof. vm_compute; reflexivity. Qed.
  Example short_evidence_rejected : check 32 [Some 8] [32;9] = false.
  Proof. vm_compute; reflexivity. Qed.
  Example extra_evidence_rejected : check 14 [Some 8;None] [14;9] = false.
  Proof. vm_compute; reflexivity. Qed.
  Example wrong_argument_equality_rejected : check 14 [Some 30] [14;31] = false.
  Proof. vm_compute; reflexivity. Qed.
  Example changed_clause_sign_rejected : check 14 [Some 8] [14;8] = false.
  Proof. vm_compute; reflexivity. Qed.
  Example omitted_clause_premise_rejected : check 14 [Some 8] [14] = false.
  Proof. vm_compute; reflexivity. Qed.
  Example changed_clause_conclusion_rejected : check 14 [Some 8] [20;9] = false.
  Proof. vm_compute; reflexivity. Qed.
  Example reordered_clause_rejected : check 14 [Some 8] [9;14] = false.
  Proof. vm_compute; reflexivity. Qed.
  Example fallback_rejected : check 14 [None] C._true = false.
  Proof. vm_compute; reflexivity. Qed.
  Example invalid_argument_bound_rejected :
    argument_clause t_i funcs atoms forms [None] [99] [99] = None.
  Proof. vm_compute; reflexivity. Qed.

  (* Exported local semantic clause over actual symbolic Boolean values and
     functions. This uses the proved checker contract, not direct congruence. *)
  Lemma boolean_uf_semantic_clause :
    C.valid (Form.interp_state_var (Atom.interp_form_hatom t_i funcs checked_atoms)
      (Atom.interp_form_hatom_bv t_i funcs checked_atoms) checked_forms) [14;9].
  Proof.
    apply (check_congr_sound t_i funcs checked_atoms checked_forms
      checked_atom_table form_table_checked 14 [Some 8] [14;9]).
    vm_compute; reflexivity.
  Qed.

  Lemma boolean_uf_target : a = b -> f a = f b.
  Proof.
    intro Hab.
    pose proof boolean_uf_semantic_clause as H.
    change (Bool.eqb (f a) (f b) || (negb (Bool.eqb a b) || false) = true) in H.
    subst b; rewrite Bool.eqb_reflx in H; simpl in H.
    now apply Bool.eqb_true_iff in H.
  Qed.
End TypedTables.

(* False/false is equality; false/true is not. Check both truth and the
   contract on false endpoints without assuming the premise is true. *)
Section FalseValues.
  Variable t_i : array typ_compdec.
  Local Definition fs := funcs false false negb negb (fun _ => 0%Z)
    0%Z 1%Z (fun _ z => z) (fun _ => false) t_i.
  Example false_false_equality_accepted :
    equality_view t_i fs atoms forms 8 = Some (1,2) /\
    Lit.interp (Form.interp_state_var (Atom.interp_form_hatom t_i fs atoms)
      (Atom.interp_form_hatom_bv t_i fs atoms) forms) 8 = true.
  Proof. vm_compute; split; reflexivity. Qed.
  Example false_false_congruence_accepted :
    check_congr t_i fs atoms forms 14 [Some 8] [14;9] = true.
  Proof. vm_compute; reflexivity. Qed.
  Example nonboolean_projection_is_really_true :
    Lit.interp (Form.interp_state_var (Atom.interp_form_hatom t_i fs atoms)
      (Atom.interp_form_hatom_bv t_i fs atoms) forms) 28 = true /\
    Atom.interp_hatom t_i fs atoms 9 <> Atom.interp_hatom t_i fs atoms 10.
  Proof.
    split; [vm_compute; reflexivity | ].
    intro H.
    change (Atom.Bval t_i Typ.TZ 0%Z = Atom.Bval t_i Typ.TZ 1%Z) in H.
    apply Atom.Bval_inj2 in H; discriminate.
  Qed.
  Local Definition ft := funcs false true (fun z => z) negb (fun _ => 0%Z)
    0%Z 1%Z (fun _ z => z) (fun _ => false) t_i.
  Example false_premise_is_conditional :
    equality_view t_i ft atoms forms 8 = Some (1,2) /\
    Lit.interp (Form.interp_state_var (Atom.interp_form_hatom t_i ft atoms)
      (Atom.interp_form_hatom_bv t_i ft atoms) forms) 8 = false /\
    Lit.interp (Form.interp_state_var (Atom.interp_form_hatom t_i ft atoms)
      (Atom.interp_form_hatom_bv t_i ft atoms) forms) 14 = false /\
    C.valid (Form.interp_state_var (Atom.interp_form_hatom t_i ft atoms)
      (Atom.interp_form_hatom_bv t_i ft atoms) forms) [14;9].
  Proof. vm_compute; repeat split; reflexivity. Qed.
End FalseValues.
End EunoiaBoolTests.

Print Assumptions EunoiaBoolTests.boolean_uf_semantic_clause.
Print Assumptions EunoiaBoolTests.boolean_uf_target.
Print Assumptions EunoiaBoolTests.false_false_equality_accepted.
Print Assumptions EunoiaBoolTests.nonboolean_projection_is_really_true.
Print Assumptions EunoiaBoolTests.false_premise_is_conditional.
