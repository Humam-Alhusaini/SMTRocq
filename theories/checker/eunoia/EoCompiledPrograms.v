(* SMTCoq -- distributed under the CeCILL-C licence (see LICENSE). *)
From Stdlib Require Import List String Bool Arith Lia.
From SMTCoq.checker.eunoia Require Import EoSyntax EoRuntime EoCheckedMemo.
From SMTCoq.checker.eunoia Require Import EoStaged EoFuelLayers.
Import ListNotations EoCheckedMemo.
Open Scope string_scope.
Module EoCompiledPrograms.
Lemma named_map_values : forall A B (f:A->B) entries name,
 named name (map (fun kv=>(fst kv,f(snd kv))) entries)=option_map f (named name entries).
Proof.
 intros A B f entries; induction entries as [|[key value] entries IH];intros name;simpl;[reflexivity|].
 destruct (String.eqb name key);[reflexivity|apply IH].
Qed.
Section Programs.
 Variable nilof:nil_query.
 Variable extra:primitive_hook.
 Variable ops:list(string*term).
 Variable typeof:term->option term.
 Variable programs:list(string*program).
 Definition code := EoStaged.handler -> nat -> bindings -> computation term.
 Definition compile_cases (cases:list program_case) : list(list pattern*code) :=
 map(fun c=>(case_patterns c,EoStaged.compile nilof extra ops typeof programs (case_body c) 0)) cases.
 Definition compile_table :=map(fun kv=>(fst kv,compile_cases(program_cases(snd kv))))programs.
 Fixpoint select_code (cases:list(list pattern*code)) args env :=
 match cases with
 | []=>None
 | (pats,body)::rest=>match match_patterns_with nilof typeof pats args env with
   |Some bs=>Some(bs,body)|None=>select_code rest args env end
 end.
 Definition run_cases fuel calls cases args env :=
 match select_code (compile_cases cases) args env with
 |None=>Stuck|Some(bs,body)=>body calls fuel bs end.
 Lemma run_cases_correct : forall fuel calls,
 (forall depth name args,0<depth<=fuel ->calls depth name args=
 call_reference nilof extra ops (fuel-depth) typeof programs name args) ->
 forall cases args env,
 run_cases fuel calls cases args env=
 match select_case_with nilof typeof cases args env with
 |None=>Stuck|Some(bs,body)=>evaluate_computation nilof extra ops fuel typeof programs bs body end.
 Proof.
 intros fuel calls Hcall cases;induction cases as [|c cases IH];intros args env;[reflexivity|].
 unfold run_cases in *;cbn -[EoStaged.compile evaluate_computation].
 destruct (match_patterns_with nilof typeof (case_patterns c) args env) as [bs|].
 - apply (EoStaged.compile_refinement nilof extra ops typeof programs fuel calls Hcall fuel 0 bs (case_body c));lia.
 - apply IH.
 Qed.
 Definition run_compiled fuel calls name args :=
 match named name compile_table with
 |None=>Missing("program "++name)
 |Some cases=>match select_code cases args [] with
   |None=>Stuck|Some(bs,body)=>body calls fuel bs end
 end.
 Theorem run_compiled_correct : forall fuel calls,
 (forall depth name args,0<depth<=fuel ->calls depth name args=
 call_reference nilof extra ops (fuel-depth) typeof programs name args) ->
 forall name args,run_compiled fuel calls name args=call_reference nilof extra ops fuel typeof programs name args.
 Proof.
 intros fuel calls Hcall name args;unfold run_compiled,compile_table,call_reference.
 rewrite (named_map_values _ _ (fun p=>compile_cases(program_cases p)) programs name). destruct (named name programs) as [p|];[|reflexivity].
 apply run_cases_correct;exact Hcall.
 Qed.
 Definition execute fuel name args :=EoFuelLayers.run (EoFuelLayers.make run_compiled fuel) name args.
 Theorem execute_correct : forall fuel name args,
 execute fuel name args=call_reference nilof extra ops fuel typeof programs name args.
 Proof.
 intros;unfold execute.
 apply (EoFuelLayers.make_correct run_compiled (fun n=>call_reference nilof extra ops n typeof programs)).
 intros;apply run_compiled_correct;assumption.
 Qed.
End Programs.
Print Assumptions execute_correct.
End EoCompiledPrograms.
