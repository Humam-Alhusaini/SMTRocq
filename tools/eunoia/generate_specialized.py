#!/usr/bin/env python3
"""Generate independently checked rule implementations from the Eunoia signature."""
from pathlib import Path
import argparse, hashlib, json, sys
root=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(root/'tools/eunoia'))
from compile import Compiler, seq, quoted, lst
from direct_codegen import Emitter, parse_ir
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',required=True,type=Path)
parser.add_argument('--manifest',type=Path)
parser.add_argument('--reference-program',action='append',default=[],
                    help='retain reference evaluation for a named helper (repeatable)')
args=parser.parse_args()
c=Compiler(root/'tools/eunoia/signatures/cpc/Cpc.eo')
c.compile((root/'tools/eunoia/rules.txt').read_text().split())
names=sorted(c.programs)
reference=sorted(set(args.reference_program))
if set(reference)-set(names):parser.error('unknown reference helper')
ids={n:f'static_{i} nilof extra typeof'for i,n in enumerate(names)}
emit=Emitter(ids).emit
parameters='(nilof:nil_query)(extra:primitive_hook)(typeof:term->option term)'
parts=['''(* Generated from the pinned Eunoia signature; syntax computation only. *)
From Stdlib Require Import List String Bool Arith.
From SMTCoq.checker.eunoia Require Import EoSyntax EoRuntime EoRuleMemo EoCheckedMemo EoMemoCollector CpcGenerated EoDirect CpcDirectEntry EoSpecialized.
Import ListNotations EoMemoCollector EoCheckedMemo.
Open Scope string_scope.
Module CpcSpecialized.
''']
parts.append(f'''Definition program_dispatch nilof extra typeof fuel name args :=
 if existsb (String.eqb name) {lst([quoted(n)for n in reference])} then
 call_reference nilof extra cpc_operators fuel typeof cpc_programs name args
 else CpcDirectEntry.dispatch nilof extra typeof fuel name args.
Lemma program_dispatch_correct:forall nilof extra typeof fuel name args,
 program_dispatch nilof extra typeof fuel name args=call_reference nilof extra cpc_operators fuel typeof cpc_programs name args.
Proof. intros;unfold program_dispatch;destruct(existsb _ _);[reflexivity|apply CpcDirectEntry.dispatch_correct]. Qed.
''')
for i,n in enumerate(names):
 parts.append(f'Definition static_{i} {parameters} := Eval cbv beta iota zeta delta [program_dispatch existsb CpcDirectEntry.dispatch String.eqb Ascii.eqb Bool.eqb andb orb] in fun fuel args=>program_dispatch nilof extra typeof fuel {quoted(n)} args.\n')
runs=[]
run_claims=[]
for n in sorted(c.rules):
 ident='r_'+n.encode().hex()
 r=c.rules[n]
 fs=seq(c.decls[n]);scope,_,_=c.binders(fs[2]);fields={};i=3
 while i<len(fs):
  k=fs[i].value;count=2 if k==':premise-list' else 1
  fields[k]=fs[i+1:i+count+1];i+=count+1
 reqs=[tuple(c.expression(x,scope)for x in seq(pair))for pair in seq(fields[':requires'][0])] if ':requires' in fields else []
 conclusion=c.expression(fields[':conclusion'][0],scope)
 expressions=[x for pair in reqs for x in pair]+[conclusion]
 parts.append(f'Definition {ident}_rule:rule:={r}.\n')
 for j,e in enumerate(expressions):
  v=f'{ident}_expr_{j}'
  parts.append(f'Definition {v} {parameters} (fuel:nat)(env:bindings):=computed {emit(parse_ir(e),"fuel","env")}.\n')
  parts.append(f'Lemma {v}_correct:forall nilof extra typeof fuel env,{v} nilof extra typeof fuel env=evaluate_with_nils nilof extra cpc_operators fuel typeof cpc_programs env {e}.\n')
  parts.append(f'''Proof. intros;change(computed(EoDirect.compile nilof extra cpc_operators typeof cpc_programs {e} (program_dispatch nilof extra typeof) fuel env)=evaluate_with_nils nilof extra cpc_operators fuel typeof cpc_programs env {e}).
 rewrite EoDirect.compile_refinement by(intros;apply program_dispatch_correct). reflexivity. Qed.
''')
 condition='true'
 for j in reversed(range(len(reqs))):
  test=f'match {ident}_expr_{2*j} nilof extra typeof fuel env,{ident}_expr_{2*j+1} nilof extra typeof fuel env with Some x,Some y=>term_eqb x y|_,_=>false end'
  condition=f'(({test}) && {condition})'
 parts.append(f'Definition {ident}_execute {parameters} fuel env:=if {condition} then match {ident}_expr_{len(expressions)-1} nilof extra typeof fuel env with Some t=>if has_type typeof t (Symbol "Bool") then Some t else None|None=>None end else None.\n')
 parts.append(f'Lemma {ident}_execute_correct:forall nilof extra typeof fuel env,{ident}_execute nilof extra typeof fuel env=EoRuleMemo.execute_using (evaluate_with_nils nilof extra cpc_operators fuel typeof cpc_programs) typeof {ident}_rule env.\n')
 rewrites=', '.join(f'{ident}_expr_{j}_correct'for j in range(len(expressions)))
 parts.append(f'Proof. intros;unfold {ident}_execute,EoRuleMemo.execute_using;cbn [{ident}_rule rule_requires rule_conclusion forallb];rewrite {rewrites};reflexivity. Qed.\n')
 parts.append(f'Definition {ident}_run {parameters} fuel assumption args premises:=EoSpecialized.prepare_one (fun _ env=>{ident}_execute nilof extra typeof fuel env) cpc_polymorphic_operators nilof typeof cpc_operators {ident}_rule assumption args premises.\n')
 claim=f'forall nilof extra typeof fuel assumption args premises,{ident}_run nilof extra typeof fuel assumption args premises=run_rule_assuming_with_nils_polymorphic cpc_polymorphic_operators nilof extra cpc_operators fuel typeof cpc_programs cpc_rules {quoted(n)} assumption args premises'
 run_claims.append('('+claim+')')
 parts.append(f'Lemma {ident}_run_correct:{claim}.\n')
 parts.append(f'Proof. intros;unfold {ident}_run;rewrite EoRuleMemo.reference_factorization;erewrite EoSpecialized.prepare_one_correct by reflexivity;apply EoSpecialized.prepare_one_ext;intros;apply {ident}_execute_correct. Qed.\n')
 runs.append((n,ident))
for n,ident in runs:
 # Explicit uniform parameters retain constant call signatures even when a
 # rule does not use the primitive hook, nil resolver or type query.
 parts.append(f'Definition {ident}:EoSpecialized.implementation:=EoSpecialized.Implementation {quoted(n)} (fun nilof extra fuel typeof assumption args premises=>@{ident}_run nilof extra typeof fuel assumption args premises) (fun nilof extra fuel typeof assumption args premises=>@{ident}_run_correct nilof extra typeof fuel assumption args premises).\n')
proof='I'
for _,ident in reversed(runs):proof=f'(conj {ident}_run_correct {proof})'
parts.append('(* Proof-only aggregate: audit shared dependencies once. It is never an executable registry. *)\n')
parts.append('Theorem rules_correct :\n'+' /\\\n'.join(run_claims+['True'])+'.\nProof. exact '+proof+'. Qed.\n')
parts.append('End CpcSpecialized.\n')
text=''.join(parts)
args.output.write_text(text)
if args.manifest:
 manifest={'format':1,'source_generated_sha256':hashlib.sha256((root/'theories/checker/eunoia/CpcGenerated.v').read_bytes()).hexdigest(),
           'helpers_generated_sha256':hashlib.sha256((root/'theories/checker/eunoia/CpcDirect.v').read_bytes()).hexdigest(),
           'generated_sha256':hashlib.sha256(text.encode()).hexdigest(),
           'implementations':dict(runs),'reference_programs':reference}
 args.manifest.write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
print('generated',len(runs),'specialized rules')
