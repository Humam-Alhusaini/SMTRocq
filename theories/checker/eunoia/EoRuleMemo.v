(* SMTCoq -- distributed under the CeCILL-C licence (see LICENSE). *)
From Stdlib Require Import List String Bool Arith Lia.
From SMTCoq.checker.eunoia Require Import EoSyntax EoRuntime.
From SMTCoq.checker.eunoia Require Import EoCheckedMemo.
Import ListNotations EoCheckedMemo.EoCheckedMemo.
Open Scope string_scope.
Module EoRuleMemo.
Definition with_prepared_rule {A:Type} (continue:rule -> bindings -> option A) (polymorphic : list string) (nilof : nil_query) (extra : primitive_hook) (ops : list (string * term))
    (fuel : nat) (typeof : term -> option term)
    (programs : list (string * program)) (rules : list (string * rule))
    (name : string) (assumption : option term) (args premises : list term) : option A :=
  match named name rules with
  | None => None
  | Some r =>
    let gathered :=
      match rule_premise_list r with
      | None => Some premises
      | Some op => option_map (fun terminator => [make_list (Symbol op) terminator premises]) (named op ops)
      end in
    let assumed := match rule_assumption r, assumption with
      | None, None => Some []
      | Some pat, Some t =>
          if has_type typeof t (Symbol "Bool") then match_pattern_with nilof typeof pat t [] else None
      | _, _ => None
      end in
    match gathered, assumed with
    | Some ps, Some initial =>
    match match_patterns_with nilof typeof (rule_arguments r ++ rule_premises r) (args ++ ps) initial with
    | None => None
    | Some env =>
      if Nat.eqb (List.length args) (List.length (rule_arguments r)) &&
         Nat.eqb (List.length ps) (List.length (rule_premises r)) &&
         forallb (fun t => has_type typeof t (Symbol "Bool")) premises then
        let patterns := (rule_arguments r ++ rule_premises r)%list in
        let values := (args ++ ps)%list in
        let hints := match collect_application_hints_with_polymorphic polymorphic typeof patterns values [] with
          | Some hs => match rule_assumption r, assumption with
              | Some pat, Some t => application_hints_with_polymorphic polymorphic typeof pat t None hs
              | _, _ => Some hs end
          | None => None end in
        match (match hints with Some hs => typed_bindings_with_hints typeof hs (rule_binders r) env | None => None end) with
        | None => None
        | Some checked =>
          continue r checked
        end
      else None
    end
    | _, _ => None
    end
  end.

Definition execute_using (ev:bindings->expression->option term) typeof r checked :=
 let evaluate := ev checked in
 if forallb (fun req => match evaluate (fst req), evaluate (snd req) with
   Some x,Some y=>term_eqb x y|_,_=>false end) (rule_requires r) then
 match evaluate (rule_conclusion r) with
 | Some t => if has_type typeof t (Symbol "Bool") then Some t else None
 | None => None end else None.
Lemma reference_factorization : forall polymorphic nilof extra ops fuel typeof programs rules name assumption args premises,
 run_rule_assuming_with_nils_polymorphic polymorphic nilof extra ops fuel typeof programs rules name assumption args premises =
 with_prepared_rule (execute_using (evaluate_with_nils nilof extra ops fuel typeof programs) typeof)
   polymorphic nilof extra ops fuel typeof programs rules name assumption args premises.
Proof. intros; unfold with_prepared_rule, execute_using, run_rule_assuming_with_nils_polymorphic; reflexivity. Qed.
Lemma with_prepared_rule_ext : forall A (f g:rule->bindings->option A),
 (forall r env, f r env=g r env) ->
 forall polymorphic nilof extra ops fuel typeof programs rules name assumption args premises,
 with_prepared_rule f polymorphic nilof extra ops fuel typeof programs rules name assumption args premises =
 with_prepared_rule g polymorphic nilof extra ops fuel typeof programs rules name assumption args premises.
Proof.
 intros A f g H polymorphic nilof extra ops fuel typeof programs rules name assumption args premises.
 unfold with_prepared_rule.
 repeat first [reflexivity | apply H | progress cbn beta iota zeta |
   match goal with |- context[match ?x with _ => _ end] => destruct x eqn:? end].
Qed.
Lemma forallb_extensional : forall A (f g:A->bool),
 (forall x,f x=g x) -> forall xs,forallb f xs=forallb g xs.
Proof. intros A f g H xs; induction xs; simpl; [reflexivity|now rewrite H, IHxs]. Qed.
Lemma execute_using_ext : forall f g,
 (forall env e,f env e=g env e) -> forall typeof r checked,
 execute_using f typeof r checked=execute_using g typeof r checked.
Proof.
 intros f g H typeof r checked; unfold execute_using.
 assert (Hr : forall req, (match f checked (fst req),f checked (snd req) with
   Some x,Some y=>term_eqb x y|_,_=>false end) =
   (match g checked (fst req),g checked (snd req) with
   Some x,Some y=>term_eqb x y|_,_=>false end)) by (intros; now rewrite !H).
 rewrite (forallb_extensional _ _ _ Hr). now rewrite H.
Qed.
Print Assumptions reference_factorization.
Print Assumptions with_prepared_rule_ext.
Print Assumptions execute_using_ext.
Definition run_rule_cached polymorphic nilof extra ops fuel typeof programs cache rules name assumption args premises :=
 with_prepared_rule
   (execute_using (fun env e=>computed (evaluate_cached nilof extra ops fuel cache fuel 0 typeof programs env e)) typeof)
   polymorphic nilof extra ops fuel typeof programs rules name assumption args premises.
Theorem run_rule_cached_refinement : forall polymorphic nilof extra ops fuel typeof programs cache rules name assumption args premises,
 cache_valid nilof extra ops fuel typeof programs cache ->
 run_rule_cached polymorphic nilof extra ops fuel typeof programs cache rules name assumption args premises =
 run_rule_assuming_with_nils_polymorphic polymorphic nilof extra ops fuel typeof programs rules name assumption args premises.
Proof.
 intros. rewrite reference_factorization. unfold run_rule_cached.
 apply with_prepared_rule_ext. intros r env. apply execute_using_ext. intros env' e.
 rewrite evaluate_cached_refinement by (try assumption; lia). reflexivity.
Qed.
Print Assumptions run_rule_cached_refinement.

Definition surface_using (run : (term -> option term) -> string -> option term -> list term -> list term -> option term) (polymorphic : list string) (nilof : nil_query) (extra : primitive_hook) (fuel : nat)
    (typeof : term -> option term) (ops : list (string * term))
    (programs : list (string * program)) (rules : list (string * rule))
    (name : string) (assumption : option term) (args premises : list term) : option term :=
  let fix visit xs :=
    match xs with
    | [] => Some []
    | x :: tl => match surface_in_with nilof typeof fuel ops x, visit tl with Some y, Some ys => Some (y :: ys) | _, _ => None end
    end in
  let internal_type t :=
    match surface_out_with nilof typeof fuel ops t with
    | Some s => typeof s
    | _ => None
    end in
  let assumed := match assumption with
    | None => Some None
    | Some t => option_map (@Some term) (surface_in_with nilof typeof fuel ops t)
    end in
  match visit args, visit premises, assumed with
  | Some xs, Some ps, Some a =>
    match run internal_type name a xs ps with
    | Some t => surface_out_with nilof typeof fuel ops t
    | _ => None
    end
  | _, _, _ => None
  end.

Definition internal_query nilof typeof fuel ops t :=
 match surface_out_with nilof typeof fuel ops t with Some s=>typeof s|_=>None end.
Definition run_surface_cached polymorphic nilof extra fuel typeof ops programs cache rules name assumption args premises :=
 surface_using (fun query=>run_rule_cached polymorphic nilof extra ops fuel query programs cache rules)
 polymorphic nilof extra fuel typeof ops programs rules name assumption args premises.
Theorem run_surface_cached_refinement : forall polymorphic nilof extra fuel typeof ops programs cache rules name assumption args premises,
 cache_valid nilof extra ops fuel (internal_query nilof typeof fuel ops) programs cache ->
 run_surface_cached polymorphic nilof extra fuel typeof ops programs cache rules name assumption args premises =
 run_surface_rule_assuming_with_nils_polymorphic polymorphic nilof extra fuel typeof ops programs rules name assumption args premises.
Proof.
 intros. unfold run_surface_cached, surface_using, run_surface_rule_assuming_with_nils_polymorphic.
 fold (internal_query nilof typeof fuel ops).
 repeat first [reflexivity | rewrite run_rule_cached_refinement by assumption |
   match goal with |- context[match ?x with _=>_ end]=>destruct x eqn:? end].
Qed.
Print Assumptions run_surface_cached_refinement.
End EoRuleMemo.
