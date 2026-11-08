(* SMTCoq -- distributed under the CeCILL-C licence (see LICENSE).
   Local derivations using the existing SMTCoq operations and strict gates. *)
From Stdlib Require Import List Bool Uint63.
From SMTCoq.utils Require Import PArray CompDec.
From SMTCoq.checker.fol Require Import State Terms.
From SMTCoq.checker.eunoia Require Import EunoiaLocal.
Import ListNotations.
Local Open Scope uint63_scope.
Module EunoiaLocalDirect.
Module L := EunoiaLocal.
Section Tables.
Variable t_i : array typ_compdec.
Variable t_func : array (Atom.tval t_i).
Variable t_atom : array Atom.atom.
Variable t_form : array Form.form.
Definition prepared_gate (ready : bool) : list C.t -> C.t -> L.witness -> bool :=
 fun cs c w => ready && L.clause_wf (PArray.length t_form) c &&
 match L.load_roots (PArray.length t_form) (L.initial (L.capacity w)) cs (L.root_claims w) with
 | None => false
 | Some m => match @L.run t_i t_func t_atom t_form m (L.program w) with
   | None => false
   | Some m' => L.available m' (L.conflict w) &&
       L.clause_eqb (S.get (L.clauses m') (L.conflict w)) c
   end
 end.
Definition gate := prepared_gate (Form.check_form t_form && Atom.check_atom t_atom).
Theorem gate_correct : Atom.wt t_i t_func t_atom = true ->
 forall cs c w, gate cs c w = true ->
 Forall (C.valid (@L.valuation t_i t_func t_atom t_form)) cs ->
 C.valid (@L.valuation t_i t_func t_atom t_form) c.
Proof.
 intros Hwt cs c w Hgate Hcs; unfold gate, prepared_gate in Hgate.
 rewrite !andb_true_iff in Hgate.
 destruct Hgate as [[[Hform Hatom] Hc] Hgate].
 destruct (L.load_roots (PArray.length t_form) (L.initial (L.capacity w)) cs
   (L.root_claims w)) as [m|] eqn:Hl; [|discriminate].
 destruct (@L.run t_i t_func t_atom t_form m (L.program w)) as [m'|] eqn:Hr; [|discriminate].
 apply andb_true_iff in Hgate; destruct Hgate as [_ Hconcl].
 apply L.clause_eqb_spec in Hconcl.
 assert (Hwf : Valuation.wf (@L.valuation t_i t_func t_atom t_form)).
 { unfold L.valuation; apply (proj2 (Form.check_form_correct _ _ _ Hform)). }
 assert (Hm : S.valid (@L.valuation t_i t_func t_atom t_form) (L.clauses m)).
 { eapply L.load_roots_valid; [exact Hwf|exact Hcs| |exact Hl].
   apply S.valid_make; exact Hwf. }
 assert (Hm' : S.valid (@L.valuation t_i t_func t_atom t_form) (L.clauses m')).
 { eapply L.run_valid; eassumption. }
 specialize (Hm' (L.conflict w)); now rewrite Hconcl in Hm'.
Qed.
End Tables.
Print Assumptions gate_correct.
End EunoiaLocalDirect.
