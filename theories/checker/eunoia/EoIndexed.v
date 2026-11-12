(* SMTCoq -- distributed under the CeCILL-C licence (see LICENSE). *)
From Stdlib Require Import List String Bool Arith.
From SMTCoq.checker.eunoia Require Import EoSyntax EoRuntime EoCheckedMemo EoRuleMemo.
Import ListNotations EoCheckedMemo.
Open Scope string_scope.
Module EoIndexed.
Fixpoint evaluate_indexed (nilof : nil_query) (extra : primitive_hook)
    (ops : list (string * term)) (fuel : nat) (typeof : term -> option term)
    (get_program : string -> option program) (env : bindings) (e : expression)
    : computation term :=
  match fuel with
  | O => Missing "fuel exhausted"
  | S k =>
    let ev := evaluate_indexed nilof extra ops k typeof get_program env in
    let fix eval_args (xs : list expression) : computation (list term) :=
      match xs with
      | [] => Done []
      | a :: tl =>
          match ev a, eval_args tl with
          | Done t, Done ts => Done (t :: ts)
          | Missing reason, _ => Missing reason
          | _, Missing reason => Missing reason
          | _, _ => Stuck end
      end in
    let binary a b f := match ev a, ev b with
      | Done x, Done y => f x y
      | Missing reason, _ => Missing reason
          | _, Missing reason => Missing reason
      | _, _ => Stuck end in
    match e with
    | ENil op ty => bind_computation (ev ty) (fun t => match nilof op (Some t) with Some z => Done z | None => Missing ("nil " ++ op) end)
    | EVar n => match lookup n env with Some t => Done t | None => Missing "unbound variable" end
    | ESymbol s => Done (Symbol s)
    | EApply f a => binary f a (fun g b => Done (Apply g b))
    | EIsOk a => match ev a with
        | Done _ => Done (bool_term true) | Stuck => Done (bool_term false) | Missing reason => Missing reason end
    | EIsEq a b => match ev a, ev b with
        | Done x, Done y => Done (bool_term (term_eqb x y))
        | Missing reason, _ => Missing reason
          | _, Missing reason => Missing reason | _, _ => Done (bool_term false) end
    | EEq a b => binary a b (fun x y => Done (bool_term (term_eqb x y)))
    | EIf c a b => match ev c with
        | Done (Symbol "true") => ev a | Done (Symbol "false") => ev b
        | Missing reason => Missing reason | _ => Stuck end
    | ERequires a b body => binary a b (fun x y => if term_eqb x y then ev body else Stuck)
    | ETypeof a => bind_computation (ev a) (fun t => match typeof t with Some ty => Done ty | None => Missing "eo::typeof" end)
    | ELet n value body => bind_computation (ev value) (fun t =>
        evaluate_indexed nilof extra ops k typeof get_program ((n, t) :: env) body)
    | ENative name args =>
        match eval_args args with
        | Missing reason => Missing reason
        | Stuck =>
            if existsb (String.eqb name) ["eo::is_z"; "eo::is_q"; "eo::is_bin"; "eo::is_str"; "eo::is_bool"]
            then Done (bool_term false) else Stuck
        | Done ts => match native_with_nils nilof typeof extra ops name ts with
            | Some t => Done t
            | None =>
                if existsb (String.eqb name)
                    ["eo::not"; "eo::and"; "eo::or"; "eo::xor";
                     "eo::list_rev"; "eo::list_len"; "eo::list_nth"; "eo::list_find";
                     "eo::list_erase"; "eo::list_erase_all"; "eo::list_setof"; "eo::list_concat";
                     "eo::list_diff"; "eo::list_inter"; "eo::list_minclude"; "eo::list_meq";
                     "eo::list_singleton_elim"; "eo::list_singleton_intro"; "eo::list_repeat";
                     "eo::cons"; "eo::nil"] then Stuck
                else match extra "eo::supports" [Symbol name] with
                | Some (Symbol "true") => Stuck | _ => Missing name end
            end
        end
    | ECall name args =>
        match get_program name, eval_args args with
        | Some p, Done ts =>
            match select_case_with nilof typeof (program_cases p) ts [] with
            | Some (bs, body) => evaluate_indexed nilof extra ops k typeof get_program bs body
            | None => Stuck end
        | None, _ => Missing ("program " ++ name)
        | _, Missing reason => Missing reason
        | _, _ => Stuck
        end
    end
  end.

Theorem evaluate_indexed_refinement : forall nilof extra ops typeof programs get_program,
 (forall name,get_program name=named name programs) -> forall fuel env e,
 evaluate_indexed nilof extra ops fuel typeof get_program env e=
 evaluate_computation nilof extra ops fuel typeof programs env e.
Proof.
 intros nilof extra ops typeof programs get_program Hget fuel.
 induction fuel as [|fuel IH]; intros env e; [reflexivity|].
 destruct e; cbn [evaluate_indexed evaluate_computation].
 all: fold evaluate_indexed evaluate_computation.
 all: try (repeat rewrite IH; reflexivity).
 all: try (unfold bind_computation; rewrite IH;
   destruct (evaluate_computation nilof extra ops fuel typeof programs env e1); try reflexivity; apply IH).
 all: try reflexivity.
 all: try rewrite Hget.
 all: fold (arguments (evaluate_indexed nilof extra ops fuel typeof get_program env)).
 all: fold (arguments (evaluate_computation nilof extra ops fuel typeof programs env)).
 all: rewrite (arguments_ext _ _ (IH env)).
 all: try reflexivity.
 destruct (named s programs) as [p|]; [|reflexivity].
 destruct (arguments (evaluate_computation nilof extra ops fuel typeof programs env) l)
   as [ts| |reason]; try reflexivity.
 destruct (select_case_with nilof typeof (program_cases p) ts []) as [[bs body]|];
   try reflexivity; apply IH.
Qed.
Print Assumptions evaluate_indexed_refinement.


Definition run_rule polymorphic nilof extra ops fuel typeof programs get_program rules name assumption args premises :=
 EoRuleMemo.with_prepared_rule
 (EoRuleMemo.execute_using (fun env e=>computed(evaluate_indexed nilof extra ops fuel typeof get_program env e)) typeof)
 polymorphic nilof extra ops fuel typeof programs rules name assumption args premises.
Theorem run_rule_refinement : forall polymorphic nilof extra ops fuel typeof programs get_program rules name assumption args premises,
 (forall key,get_program key=named key programs) ->
 run_rule polymorphic nilof extra ops fuel typeof programs get_program rules name assumption args premises=
 run_rule_assuming_with_nils_polymorphic polymorphic nilof extra ops fuel typeof programs rules name assumption args premises.
Proof.
 intros. rewrite EoRuleMemo.reference_factorization. unfold run_rule.
 apply EoRuleMemo.with_prepared_rule_ext. intros r env.
 apply EoRuleMemo.execute_using_ext. intros env' e.
 rewrite (evaluate_indexed_refinement nilof extra ops typeof programs get_program H fuel env' e). reflexivity.
Qed.
Definition run_surface polymorphic nilof extra fuel typeof ops programs get_program rules name assumption args premises :=
 EoRuleMemo.surface_using (fun query=>run_rule polymorphic nilof extra ops fuel query programs get_program rules)
 polymorphic nilof extra fuel typeof ops programs rules name assumption args premises.
Theorem run_surface_refinement : forall polymorphic nilof extra fuel typeof ops programs get_program rules name assumption args premises,
 (forall key,get_program key=named key programs) ->
 run_surface polymorphic nilof extra fuel typeof ops programs get_program rules name assumption args premises=
 run_surface_rule_assuming_with_nils_polymorphic polymorphic nilof extra fuel typeof ops programs rules name assumption args premises.
Proof.
 intros. unfold run_surface,EoRuleMemo.surface_using,run_surface_rule_assuming_with_nils_polymorphic.
 repeat first [reflexivity|rewrite run_rule_refinement by assumption|
   match goal with |- context[match ?x with _=>_ end]=>destruct x eqn:? end].
Qed.
Print Assumptions run_surface_refinement.
End EoIndexed.
