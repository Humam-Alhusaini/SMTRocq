(* SMTCoq -- distributed under the CeCILL-C licence (see LICENSE). *)
From Stdlib Require Import List String Bool Arith Lia.
From SMTCoq.checker.eunoia Require Import EoSyntax EoRuntime CpcGenerated EoCheckedMemo.
From SMTCoq.checker.eunoia Require Import EoStaged EoFuelLayers EoCompiledPrograms.
Import ListNotations EoCheckedMemo.
Open Scope string_scope.
Module CpcStaged.
Section Context.
 Variable nilof:nil_query.
 Variable extra:primitive_hook.
 Variable typeof:term->option term.
 Definition code_table := Eval cbv [EoCompiledPrograms.compile_table EoCompiledPrograms.compile_cases
 EoStaged.compile cpc_programs map fst snd program_cases case_patterns case_body
 named String.eqb Ascii.eqb Bool.eqb andb orb] in
 EoCompiledPrograms.compile_table nilof extra cpc_operators typeof cpc_programs.
 Definition build_with table fuel calls name args :=
 match named name table with
 |None=>Missing("program "++name)
 |Some cases=>match EoCompiledPrograms.select_code nilof typeof cases args [] with
   |None=>Stuck|Some(bs,body)=>body calls fuel bs end
 end.
 Definition build := build_with code_table.
 Lemma build_reference : forall fuel calls name args,
 build fuel calls name args=
 EoCompiledPrograms.run_compiled nilof extra cpc_operators typeof cpc_programs fuel calls name args.
 Proof. reflexivity. Qed.
 Definition execute fuel name args:=
 let table:=code_table in EoFuelLayers.run(EoFuelLayers.make (build_with table) fuel)name args.
 Theorem execute_correct : forall fuel name args,
 execute fuel name args=call_reference nilof extra cpc_operators fuel typeof cpc_programs name args.
 Proof.
 intros;unfold execute.
 apply(EoFuelLayers.make_correct build (fun n=>call_reference nilof extra cpc_operators n typeof cpc_programs)).
 intros. rewrite build_reference. apply EoCompiledPrograms.run_compiled_correct;assumption.
 Qed.
End Context.
Print Assumptions execute_correct.
End CpcStaged.
