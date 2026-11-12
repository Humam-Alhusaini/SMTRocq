(* Distributed under the CeCILL-C license; see LICENSE.
   SMTRocq's CVC5 tactics build upon SMTCoq's preprocessing and checkers.
   The Eunoia/CPC checker is supplied by the pinned external repository. *)
From Stdlib Require Import Uint63 List Bool ZArith.
From Trakt Require Import Trakt.
From Ltac2 Require Import Ltac2 Bool.
From SMTCoq.tactics Require Export Tactics.
From SMTCoq.utils Require Import Misc PArray.
From SMTCoq.tactics Require Import QInst.
From SMTCoq.tactics.preproc Require Import Conversion EunoiaFrontend.
From SMTCoq.checker.eunoia Require Import EunoiaTactic EunoiaScopedAdapter.
Set Default Proof Mode "Classic".

(* cvc5 CPC/Eunoia, with the generated evaluator and concrete semantic gate. *)
Ltac2 cvc5_tac_with_backend compiled fast global :=
  Control.enter (fun () =>
    ltac1:(intros; unfold is_true in *);
    (* Kernel equality elimination avoids passing a formula-valued Boolean
       constant as a UF atom to the legacy SMT-LIB reifier. Normalize before
       capturing local proof terms. Explicit supplied lemmas keep their
       original context and follow the unchanged path. *)
    (match global with
     | [] => ltac1:(repeat match goal with
         | H : ?x = true |- _ => is_var x; subst x
         | H : true = ?x |- _ => is_var x; subst x
         | H : ?x = false |- _ => is_var x; subst x
         | H : false = ?x |- _ => is_var x; subst x
         end)
     | _ => ()
     end);
    let run r := if compiled then
      ltac1:(r |- cvc5_smtcoq_bool_base r) (Ltac1.of_constr r)
      else ltac1:(r |- cvc5_eunoia_bool_base r) (Ltac1.of_constr r) in
    let legacy () :=
      let local := List.map (fun (id, _) => (Some id, Control.hyp id)) (get_hyps_prop ()) in
      let global := List.map (fun t => (None, t)) global in
      let hsglob := pose_hyps global [] in
      let hs := pose_hyps local hsglob in
      preprocess1 true hs;
      let n := Control.numgoals () in
      Control.focus n n (fun () =>
        let hs' := preprocess2 hs in
        let r := tupleify (List.map Control.hyp hs') in
        run r
      );
      ltac1:(QInst.vauto) in
    match global with
    | [] => if fast then
        Control.plus
          (fun () =>
            let (r,back) := EunoiaFrontend.prepare () in
            ltac1:(back |- apply back) (Ltac1.of_constr back);
            run r)
          (fun _ => legacy ())
      else legacy ()
    | _ => legacy ()
    end
  ).

Ltac2 cvc5_eunoia_tac_with_fast_preprocessing fast global :=
 cvc5_tac_with_backend false fast global.
Ltac2 smtrocq_tac global := cvc5_tac_with_backend true true global.
Ltac2 cvc5_eunoia_tac global := cvc5_eunoia_tac_with_fast_preprocessing true global.

(* The fast tactic checks compiled SMTCoq certificates. The strict CPC tactic
   below additionally certifies signature-generated source conformance. *)
Tactic Notation "smtrocq" := ltac2:(smtrocq_tac []).
Tactic Notation "smtrocq" constr(h) :=
  let tac := ltac2:(h |- smtrocq_tac (global_of_ltac1_constr h)) in tac h.
Tactic Notation "cvc5_eunoia" := ltac2:(cvc5_eunoia_tac []).
Tactic Notation "cvc5_eunoia" constr(h) :=
  let tac := ltac2:(h |- cvc5_eunoia_tac (global_of_ltac1_constr h)) in
  tac h.
