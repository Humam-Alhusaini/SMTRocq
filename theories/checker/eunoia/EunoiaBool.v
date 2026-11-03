(**************************************************************************)
(* SMTCoq -- distributed under the terms of the CeCILL-C licence            *)
(**************************************************************************)

From Stdlib Require Import Bool List Uint63.
From SMTCoq.utils Require Import Misc PArray CompDec.
From SMTCoq.checker.fol Require Import State Terms.

Import ListNotations.
Local Open Scope uint63_scope.
Local Open Scope array_scope.

(* A local semantic certificate, independent of CPC rules. All failure paths
   return None/false, including malformed indices and unsupported polarity.
   No new atom, formula, interpretation, or trusted operation is introduced. *)
Module EunoiaBool.
Section Certificate.
  Variables (t_i : array typ_compdec) (t_func : array (Atom.tval t_i))
            (t_atom : array Atom.atom) (t_form : array Form.form).

  Definition atom_view (l : _lit) : option Atom.hatom :=
    if Lit.is_pos l && (Lit.blit l <? length t_form) then
      match t_form.[Lit.blit l] with
      | Form.Fatom a => if a <? length t_atom then Some a else None
      | _ => None
      end
    else None.

  Definition typed_pair (t : Typ.type) (a b : Atom.hatom) : bool :=
    (a <? length t_atom) && (b <? length t_atom) &&
    Typ.eqb (Atom.get_type t_i t_func t_atom a) t &&
    Typ.eqb (Atom.get_type t_i t_func t_atom b) t.

  (* Fiff operands must denote actual Boolean atoms. Merely projecting their
     values to bool is unsound: [interp_bool] defaults to true on other types.
     Negative equality literals and negative Fiff operands are rejected;
     they do not assert equality of the underlying atom values. *)
  Definition equality_view (l : _lit) : option (Atom.hatom * Atom.hatom) :=
    if Lit.is_pos l && (Lit.blit l <? length t_form) then
      match t_form.[Lit.blit l] with
      | Form.Fatom e =>
        if e <? length t_atom then
          match t_atom.[e] with
          | Atom.Abop (Atom.BO_eq t) a b =>
            if typed_pair t a b then Some (a, b) else None
          | _ => None
          end
        else None
      | Form.Fiff p q =>
        match atom_view p, atom_view q with
        | Some a, Some b =>
          if typed_pair Typ.Tbool a b then Some (a, b) else None
        | _, _ => None
        end
      | _ => None
      end
    else None.

  Definition endpoints (a b x y : Atom.hatom) : bool :=
    ((a =? x) && (b =? y)) || ((a =? y) && (b =? x)).

  (* One optional equality per argument; None means syntactic reflexivity.
     This checks length as well as every argument, including unchanged ones. *)
  Fixpoint argument_clause (eqs : list (option _lit))
      (xs ys : list Atom.hatom) : option C.t :=
    match eqs, xs, ys with
    | [], [], [] => Some []
    | e :: es, a :: xs, b :: ys =>
      if (a <? length t_atom) && (b <? length t_atom) then
        match e with
        | None => if a =? b then argument_clause es xs ys else None
        | Some l =>
          match equality_view l, argument_clause es xs ys with
          | Some (x, y), Some c =>
            if endpoints a b x y then Some (Lit.neg l :: c) else None
          | _, _ => None
          end
        end
      else None
    | _, _, _ => None
    end.

  (* UF application congruence, with arbitrary result/argument sorts. The
     result and each premise can independently use BO_eq or typed Fiff. *)
  Definition congr_clause (res : _lit) (eqs : list (option _lit)) : option C.t :=
    match equality_view res with
    | Some (a, b) =>
      match t_atom.[a], t_atom.[b] with
      | Atom.Aapp f xs, Atom.Aapp g ys =>
        if (f =? g) && (f <? length t_func) then
          match argument_clause eqs xs ys with
          | Some c => Some (res :: c)
          | None => None
          end
        else None
      | _, _ => None
      end
    | None => None
    end.

  (* Exact ordered clause binding; no fallback clause counts as success. *)
  Definition check_congr res eqs (expected : C.t) : bool :=
    match congr_clause res eqs with
    | Some c => list_beq Lit.eqb c expected
    | None => false
    end.

  Section Soundness.
    Hypotheses (ch_atom : Atom.check_atom t_atom)
               (ch_form : Form.check_form t_form).

    Let h := Atom.interp_hatom t_i t_func t_atom.
    Let rho := Form.interp_state_var
      (Atom.interp_form_hatom t_i t_func t_atom)
      (Atom.interp_form_hatom_bv t_i t_func t_atom) t_form.

    Let wf_atom : Atom.wf t_atom := proj1 (Atom.check_atom_correct _ ch_atom).
    Let def_atom : default t_atom = Atom.Acop Atom.CO_xH :=
      proj2 (Atom.check_atom_correct _ ch_atom).

    Lemma form_unfold x :
      rho x = Form.interp (Atom.interp_form_hatom t_i t_func t_atom)
        (Atom.interp_form_hatom_bv t_i t_func t_atom) t_form t_form.[x].
    Proof.
      destruct (Form.check_form_correct
        (Atom.interp_form_hatom t_i t_func t_atom)
        (Atom.interp_form_hatom_bv t_i t_func t_atom) _ ch_form)
        as [[Hd Hw] _].
      exact (Form.wf_interp_form _ _ _ Hd Hw x).
    Qed.

    Lemma atom_unfold a : h a = Atom.interp t_i t_func t_atom t_atom.[a].
    Proof. exact (Atom.t_interp_wf t_i t_func t_atom wf_atom def_atom a). Qed.

    Lemma typed_pair_types t a b : typed_pair t a b = true ->
      Atom.get_type t_i t_func t_atom a = t /\
      Atom.get_type t_i t_func t_atom b = t.
    Proof.
      unfold typed_pair; rewrite !andb_true_iff.
      intros [[[_ _] Ha] Hb]; split; apply Typ.eqb_spec; assumption.
    Qed.

    Lemma atom_view_sound l a : atom_view l = Some a ->
      Lit.interp rho l = Atom.interp_bool t_i (h a).
    Proof.
      unfold atom_view.
      destruct (Lit.is_pos l && (Lit.blit l <? length t_form)) eqn:H;
        [ | discriminate].
      apply andb_true_iff in H as [Hp _].
      destruct t_form.[Lit.blit l] eqn:Hf; try discriminate.
      destruct (i <? length t_atom); [ | discriminate].
      intro E; inversion E; subst.
      unfold Lit.interp; rewrite Hp; unfold Var.interp.
      rewrite form_unfold, Hf; reflexivity.
    Qed.

    Lemma boolean_values a b : typed_pair Typ.Tbool a b = true ->
      (Bool.eqb (Atom.interp_bool t_i (h a))
                (Atom.interp_bool t_i (h b)) = true <-> h a = h b).
    Proof.
      intro H; apply typed_pair_types in H as [Ha Hb].
      generalize (Atom.check_aux_interp_hatom t_i t_func t_atom wf_atom a),
        (Atom.check_aux_interp_hatom t_i t_func t_atom wf_atom b).
      unfold Atom.get_type in Ha, Hb; rewrite Ha, Hb.
      intros [va Hva] [vb Hvb].
      fold (Atom.interp_hatom t_i t_func t_atom a) in Hva.
      fold (Atom.interp_hatom t_i t_func t_atom b) in Hvb.
      fold h in Hva, Hvb.
      rewrite Hva, Hvb; unfold Atom.interp_bool; simpl.
      rewrite Bool.eqb_true_iff.
      split; [intro E; now subst | apply Atom.Bval_inj2].
    Qed.

    Lemma atomic_equality t a b : typed_pair t a b = true ->
      (Atom.interp_bool t_i
        (Atom.apply_binop t_i t t Typ.Tbool (Typ.i_eqb t_i t) (h a) (h b)) = true
       <-> h a = h b).
    Proof.
      intro H; apply typed_pair_types in H as [Ha Hb].
      generalize (Atom.check_aux_interp_hatom t_i t_func t_atom wf_atom a),
        (Atom.check_aux_interp_hatom t_i t_func t_atom wf_atom b).
      unfold Atom.get_type in Ha, Hb; rewrite Ha, Hb.
      intros [va Hva] [vb Hvb].
      fold (Atom.interp_hatom t_i t_func t_atom a) in Hva.
      fold (Atom.interp_hatom t_i t_func t_atom b) in Hvb.
      fold h in Hva, Hvb.
      rewrite Hva, Hvb; unfold Atom.apply_binop, Atom.interp_bool; simpl.
      rewrite !Typ.cast_refl; simpl.
      change (is_true (Typ.i_eqb t_i t va vb) <->
        Atom.Bval t_i t va = Atom.Bval t_i t vb).
      rewrite Typ.i_eqb_spec.
      split; [intro E; now subst | apply Atom.Bval_inj2].
    Qed.

    (* Equivalence, not just implication: needed for both premises and result.
       In particular false/false Boolean endpoints still assert equality. *)
    Lemma equality_view_sound l a b : equality_view l = Some (a, b) ->
      (Lit.interp rho l = true <-> h a = h b).
    Proof.
      unfold equality_view.
      destruct (Lit.is_pos l && (Lit.blit l <? length t_form)) eqn:Hp;
        [ | discriminate].
      apply andb_true_iff in Hp as [Hp _].
      destruct t_form.[Lit.blit l] eqn:Hf; try discriminate.
      - destruct (i <? length t_atom); [ | discriminate].
        destruct t_atom.[i] eqn:He; try discriminate.
        destruct b0; try discriminate.
        destruct (typed_pair t i0 i1) eqn:Ht; [ | discriminate].
        intro E; inversion E; subst.
        unfold Lit.interp; rewrite Hp; unfold Var.interp.
        rewrite form_unfold, Hf; simpl.
        unfold Atom.interp_form_hatom; fold h.
        rewrite atom_unfold, He; simpl.
        now apply atomic_equality.
      - destruct (atom_view i) as [x | ] eqn:Hx; [ | discriminate].
        destruct (atom_view i0) as [y | ] eqn:Hy; [ | discriminate].
        destruct (typed_pair Typ.Tbool x y) eqn:Ht; [ | discriminate].
        intro E; inversion E; subst.
        unfold Lit.interp at 1; rewrite Hp; unfold Var.interp.
        rewrite form_unfold, Hf; simpl.
        change (Bool.eqb (Lit.interp rho i) (Lit.interp rho i0) = true <-> h a = h b).
        rewrite (atom_view_sound _ _ Hx), (atom_view_sound _ _ Hy).
        now apply boolean_values.
    Qed.

    Lemma endpoints_sound a b x y : endpoints a b x y = true ->
      h x = h y -> h a = h b.
    Proof.
      unfold endpoints; rewrite orb_true_iff, !andb_true_iff, !Uint63.eqb_spec.
      intros [[-> ->] | [-> ->]] E; congruence.
    Qed.

    Lemma argument_clause_sound eqs xs ys c :
      argument_clause eqs xs ys = Some c ->
      C.interp rho c = false -> List.map h xs = List.map h ys.
    Proof.
      revert xs ys c; induction eqs as [ | e es IH];
        intros [ | a xs] [ | b ys] c; simpl; try discriminate.
      - intros E _; inversion E; reflexivity.
      - destruct ((a <? length t_atom) && (b <? length t_atom)); [ | discriminate].
        destruct e as [l | ].
        + destruct (equality_view l) as [[x y] | ] eqn:He; [ | discriminate].
          destruct (argument_clause es xs ys) as [d | ] eqn:Hd; [ | discriminate].
          destruct (endpoints a b x y) eqn:Hab; [ | discriminate].
          intro E; inversion E; subst c.
          change (Lit.interp rho (Lit.neg l) || C.interp rho d = false ->
            h a :: map h xs = h b :: map h ys).
          rewrite orb_false_iff, Lit.interp_neg, negb_false_iff.
          intros [Hl Hc]; f_equal.
          * apply (endpoints_sound _ _ _ _ Hab).
            now apply (equality_view_sound _ _ _ He).
          * exact (IH _ _ _ Hd Hc).
        + destruct (a =? b) eqn:Hab; [ | discriminate].
          apply Uint63.eqb_spec in Hab; subst b.
          intros H Hc; f_equal; exact (IH _ _ _ H Hc).
    Qed.

    Lemma congr_clause_sound res eqs c : congr_clause res eqs = Some c ->
      C.valid rho c.
    Proof.
      unfold congr_clause.
      destruct (equality_view res) as [[a b] | ] eqn:He; [ | discriminate].
      destruct t_atom.[a] eqn:Ha; try discriminate.
      destruct t_atom.[b] eqn:Hb; try discriminate.
      destruct ((i =? i0) && (i <? length t_func)) eqn:Hfg; [ | discriminate].
      apply andb_true_iff in Hfg as [Hfg _].
      apply Uint63.eqb_spec in Hfg; subst i0.
      destruct (argument_clause eqs l l0) as [d | ] eqn:Hd; [ | discriminate].
      intro E; inversion E; subst c.
      change (Lit.interp rho res || C.interp rho d = true).
      destruct (C.interp rho d) eqn:Hc; [apply orb_true_r | rewrite orb_false_r].
      apply (equality_view_sound _ _ _ He).
      pose proof (argument_clause_sound _ _ _ _ Hd Hc) as Hargs.
      rewrite !atom_unfold, Ha, Hb; simpl.
      unfold h in Hargs; rewrite Hargs; reflexivity.
    Qed.

    Lemma check_congr_sound res eqs expected :
      check_congr res eqs expected = true -> C.valid rho expected.
    Proof.
      unfold check_congr.
      destruct (congr_clause res eqs) as [c | ] eqn:Hc; [ | discriminate].
      intro H.
      apply (proj1 (list_beq_spec int Lit.eqb Lit.eqb_spec c expected)) in H.
      subst; now apply (congr_clause_sound _ _ _ Hc).
    Qed.
  End Soundness.
End Certificate.
End EunoiaBool.

Print Assumptions EunoiaBool.form_unfold.
Print Assumptions EunoiaBool.atom_unfold.
Print Assumptions EunoiaBool.typed_pair_types.
Print Assumptions EunoiaBool.atom_view_sound.
Print Assumptions EunoiaBool.boolean_values.
Print Assumptions EunoiaBool.atomic_equality.
Print Assumptions EunoiaBool.equality_view_sound.
Print Assumptions EunoiaBool.endpoints_sound.
Print Assumptions EunoiaBool.argument_clause_sound.
Print Assumptions EunoiaBool.congr_clause_sound.
Print Assumptions EunoiaBool.check_congr_sound.
