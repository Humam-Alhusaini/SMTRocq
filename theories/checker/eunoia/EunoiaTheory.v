(* SMTCoq -- distributed under the CeCILL-C licence (see LICENSE).
   Direct theory certificates reuse the verified SMTCoq small checkers.
   Complete signature-generated source checking remains outside this gate. *)
From Stdlib Require Import List Bool Uint63 ZMicromega.
From SMTCoq.utils Require Import PArray CompDec.
From SMTCoq.checker.fol Require Import State Terms.
From SMTCoq.checker.small_checker.euf Require Import EUF.
From SMTCoq.checker.small_checker.lia Require Import LIA.
From SMTCoq.checker.eunoia Require Import EunoiaChecker EunoiaLocal.
Import ListNotations.
Local Open Scope uint63_scope.
Set Implicit Arguments.
Module EunoiaTheory.

Inductive certificate :=
| Truth
| Identity
| Trans
| Congruence (arguments : list (option _lit))
| Linear (proof : list ZMicromega.ZArithProof).

(* No caller-provided truth flags or root claims. Actual ordered premises are
   read from the scoped source checker. Nonunit premises use the old gate. *)
Fixpoint units (cs : list C.t) : option (list _lit) :=
 match cs with
 | [] => Some []
 | [l] :: rest => match units rest with Some ls => Some (l :: ls) | None => None end
 | _ => None
 end.
Lemma units_exact : forall cs ls, units cs = Some ls -> cs = map (fun l => [l]) ls.
Proof.
 induction cs as [|c cs IH]; intros ls H; cbn in H.
 - inversion H; reflexivity.
 - destruct c as [|l [|extra rest]]; try discriminate.
   destruct (units cs) as [ls'|] eqn:E; try discriminate.
   inversion H; subst; cbn; now rewrite (IH _ eq_refl).
Qed.
Definition implication ls c := S.sort (c ++ map Lit.neg ls).
Section Tables.
Variable t_form : array Form.form.
Variable t_atom : array Atom.atom.
Definition checked_clause ls c w : option C.t :=
 match w with
 | Truth | Identity => None
 | Trans => match c with [l] => Some (check_trans t_form t_atom l ls) | _ => None end
 | Congruence args => match c with [l] => Some (check_congr t_form t_atom l args) | _ => None end
 | Linear proof => Some (check_micromega t_form t_atom (implication ls c) proof)
 end.
Definition global_gate (cs : list C.t) (c : C.t) w :=
 match units cs with
 | None => false
 | Some ls => match checked_clause ls c w with
   | None => false
   | Some certified =>
     (* Default true-clause results indicate failed theory checks. *)
     negb (EunoiaChecker.clause_eqb certified C._true) &&
     EunoiaChecker.clause_eqb (S.sort certified) (implication ls c)
   end
 end.
Definition prepared_gate (ready : bool) (cs : list C.t) (c : C.t) w :=
 ready && forallb (EunoiaChecker.clause_wf (PArray.length t_form)) cs &&
 EunoiaChecker.clause_wf (PArray.length t_form) c &&
 match w with
 | Truth => EunoiaChecker.clause_eqb c C._true
 | Identity => existsb (EunoiaChecker.clause_eqb c) cs
 | _ => global_gate cs c w
 end.
End Tables.
Definition gate (t_i : array typ_compdec) (_t_func : array (Atom.tval t_i))
 (t_atom : array Atom.atom) (t_form : array Form.form) :=
 prepared_gate t_form t_atom (Form.check_form t_form && Atom.check_atom t_atom).

Lemma units_valid : forall rho cs ls,
 units cs = Some ls -> Forall (C.valid rho) cs ->
 Forall (fun l => Lit.interp rho l = true) ls.
Proof.
 intros rho cs ls H; apply units_exact in H; subst cs.
 induction ls as [|l ls IH]; intros H; [constructor|].
 inversion H; subst; constructor.
 - unfold C.valid, C.interp in H2; cbn in H2; now rewrite orb_false_r in H2.
 - now apply IH.
Qed.
Lemma negations_false : forall rho ls,
 Forall (fun l => Lit.interp rho l = true) ls ->
 C.interp rho (map Lit.neg ls) = false.
Proof.
 intros rho ls H; induction H; [reflexivity|].
 change (Lit.interp rho (Lit.neg x) || C.interp rho (map Lit.neg l) = false).
 now rewrite Lit.interp_neg, H, IHForall.
Qed.
Lemma implication_correct : forall rho cs ls c,
 Valuation.wf rho -> units cs = Some ls -> Forall (C.valid rho) cs ->
 C.valid rho (implication ls c) -> C.valid rho c.
Proof.
 intros rho cs ls c Hwf Hu Hcs H.
 unfold C.valid, implication in H; rewrite S.sort_correct in H by exact Hwf.
 unfold C.interp in H; rewrite existsb_app in H.
 change (C.interp rho c || C.interp rho (map Lit.neg ls) = true) in H.
 rewrite (@negations_false rho ls (units_valid Hu Hcs)), orb_false_r in H; exact H.
Qed.
Section Correctness.
Variable t_i : array typ_compdec.
Variable t_func : array (Atom.tval t_i).
Variable t_atom : array Atom.atom.
Variable t_form : array Form.form.
Local Notation rho := (@EunoiaLocal.valuation t_i t_func t_atom t_form).
Lemma checked_clause_correct : forall ls c w certified,
 Form.check_form t_form = true -> Atom.check_atom t_atom = true ->
 Atom.wt t_i t_func t_atom = true ->
 checked_clause t_form t_atom ls c w = Some certified -> C.valid rho certified.
Proof.
 intros ls c w certified Hform Hatom Hwt H.
 destruct w; cbn [checked_clause] in H; try discriminate.
 - destruct c as [|l [|extra rest]]; try discriminate; inversion H; subst.
   unfold C.valid, EunoiaLocal.valuation; eapply valid_check_trans; eassumption.
 - destruct c as [|l [|extra rest]]; try discriminate; inversion H; subst.
   unfold C.valid, EunoiaLocal.valuation; eapply valid_check_congr; eassumption.
 - inversion H; subst; unfold EunoiaLocal.valuation; eapply valid_check_micromega; eassumption.
Qed.
Lemma global_gate_correct : forall cs c w,
 Form.check_form t_form = true -> Atom.check_atom t_atom = true ->
 Atom.wt t_i t_func t_atom = true ->
 global_gate t_form t_atom cs c w = true ->
 Forall (C.valid rho) cs -> C.valid rho c.
Proof.
 intros cs c w Hform Hatom Hwt H Hcs; unfold global_gate in H.
 destruct (units cs) as [ls|] eqn:Hu; [|discriminate].
 destruct (checked_clause t_form t_atom ls c w) as [certified|] eqn:Hcheck; [|discriminate].
 apply andb_true_iff in H; destruct H as [_ H].
 apply EunoiaChecker.clause_eqb_spec in H.
 assert (Hvalid : C.valid rho certified) by (eapply checked_clause_correct; eassumption).
 assert (Hwf : Valuation.wf rho).
 { unfold EunoiaLocal.valuation; apply (proj2 (Form.check_form_correct _ _ _ Hform)). }
 eapply implication_correct; [exact Hwf | exact Hu | exact Hcs |].
 unfold C.valid; rewrite <- H, S.sort_correct by exact Hwf; exact Hvalid.
Qed.
Theorem gate_correct : Atom.wt t_i t_func t_atom = true ->
 forall cs c w, @gate t_i t_func t_atom t_form cs c w = true ->
 Forall (C.valid rho) cs -> C.valid rho c.
Proof.
 intros Hwt cs c w H Hcs; unfold gate, prepared_gate in H.
 rewrite !andb_true_iff in H; destruct H as [[[[Hform Hatom] Hcsbounds] Hcbounds] H].
 destruct w.
 - apply EunoiaChecker.clause_eqb_spec in H; subst c.
   apply C.interp_true; unfold EunoiaLocal.valuation;
     apply (proj2 (Form.check_form_correct _ _ _ Hform)).
 - apply existsb_exists in H; destruct H as [found [Hin Heq]].
   apply EunoiaChecker.clause_eqb_spec in Heq; subst found.
   now apply (proj1 (Forall_forall _ _) Hcs c Hin).
 - eapply global_gate_correct; eassumption.
 - eapply global_gate_correct; eassumption.
 - eapply global_gate_correct; eassumption.
Qed.
End Correctness.
Print Assumptions gate_correct.
End EunoiaTheory.
