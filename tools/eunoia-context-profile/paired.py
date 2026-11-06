#!/usr/bin/env python3
"""Pair exact accepted public checker expressions in one compiler process.

Requires the experimental patch, built and already profiled. Print the actual
closed public proof, extract its checker expression (not its computed result),
and rerun both whole checkers with exactly the same arguments. Every measurement
is a fresh lemma with vm_compute, reflexivity and Qed. No evaluation is replaced.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re

spec = importlib.util.spec_from_file_location('context_run', Path(__file__).with_name('run.py'))
run = importlib.util.module_from_spec(spec)
spec.loader.exec_module(run)
P = run.profile
CONTEXTS = {
 'congruence': 'Variable A : Type. Variable HA : CompDec A. Variable f : A -> A. Variables x y : A.',
 'predicate': 'Variable A : Type. Variable HA : CompDec A. Variable p : A -> bool. Variables x y : A.',
 'lia_bounds': 'Variable x : Z.',
 'lia_normalization': 'Variables x y : Z.',
 'lia_scoped': 'Variable x : Z.',
}
REFERENCE = '''
Definition reference := @EunoiaTactic.checker_guarded.
Definition scoped_reference ti (tf : PArray.array (Atom.tval ti)) ta tfo names fuel capacity roots rt claims t goal :=
  @EunoiaScopedAdapter.checker_guarded_with ti tf ta tfo names CpcGenerated.default_primitive
    fuel capacity roots rt claims t goal.
Definition reference_b ti (tf : PArray.array (Atom.tval ti)) ta tfo names fuel capacity l b rt claims steps goal :=
  EunoiaTactic.checker_guarded ti tf ta tfo names fuel capacity (EunoiaTactic.goal_roots l b) rt claims steps goal.
Definition scoped_reference_b ti (tf : PArray.array (Atom.tval ti)) ta tfo names fuel capacity l b rt claims t goal :=
  @EunoiaScopedAdapter.checker_guarded_with ti tf ta tfo names CpcGenerated.default_primitive
    fuel capacity (EunoiaTactic.goal_roots l b) rt claims t goal.
'''
IMPORTS = '''From SMTCoq Require Import SMTCoq.
From SMTCoq.utils Require Import PArray.
From SMTCoq.checker.fol Require Import Terms.
From SMTCoq.checker.eunoia Require Import EunoiaTactic EunoiaScopedAdapter CpcGenerated.
From Stdlib Require Import ZArith Uint63.
Local Open Scope Z_scope.
Local Open Scope uint63_scope.
'''

def extract(text):
    # Select the occurrence inside the accepted equality's type, not the
    # correctness theorem's argument list. Printing All avoids notation holes.
    matches = list(re.finditer(r'\(@?(Eunoia(?:ScopedAdapter|Tactic)\.Eunoia(?:ScopedAdapter|Tactic)\.checker(?:_b)?)\s', text))
    if len(matches) != 1:
        raise ValueError('expected one exact checker/checker_b expression in the printed proof')
    m = matches[0]
    depth = 0
    for i in range(m.start(), len(text)):
        if text[i] == '(': depth += 1
        if text[i] == ')':
            depth -= 1
            if depth == 0: return text[m.start():i+1], m[1]
    raise ValueError('unbalanced printed expression')

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cases',nargs='+',choices=CONTEXTS,default=list(CONTEXTS))
    parser.add_argument('--profiles',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--repeat',type=int,default=3)
    parser.add_argument('--timeout',type=float,default=240)
    args=parser.parse_args()
    output=args.output.resolve()
    if output==P.ROOT or P.ROOT in output.parents or '\"' in str(output) or '\n' in str(output):
        parser.error('output must be an external path without quotes or newlines')
    if args.repeat<=0 or args.timeout<=0: parser.error('repeat and timeout must be positive')
    output.mkdir(exist_ok=False,parents=True)
    run.SOURCES.append('tools/eunoia-context-profile/paired.py')
    before=run.snapshot();P.write_json(output/'sources.json',before)
    metadata={'loadavg_start':os.getloadavg(),'profile_components':os.environ.get('ROCQ_PROFILE_COMPONENTS','default')}
    P.write_json(output/'metadata.json',metadata)
    flags=P.loadpath();rows=[]
    for case in args.cases:
        context=CONTEXTS[case]
        d=output/case;d.mkdir()
        print_dir=d/'print';print_dir.mkdir()
        local_flags=[*flags,'-Q',str(d),'EunoiaContextPair_'+case]
        source=args.profiles.resolve()/(case+'-1')
        proof=d/'proof'
        (d/'PrintProof.v').write_text('Require EunoiaProfile.Case.\nSet Printing All.\nSet Printing Depth 1000000.\nSet Printing Width 120.\n'
            f'Redirect "{proof}" Print EunoiaProfile.Case.profile_result.\n')
        command=[P.WRAPPER,'dune','exec','-j2','--','rocq','c','-q',*local_flags,
                 '-I',str(P.ROOT/'_build/install/default/lib'),'-Q',str(source),'EunoiaProfile',str(d/'PrintProof.v')]
        result=P.execute(command,print_dir,args.timeout)
        if result['exit_code']!=0 or result['timeout']: return 1
        expr,name=extract(proof.with_suffix('.out').read_text())
        if '...' in expr: raise ValueError('truncated printed checker expression')
        (d/'expression.txt').write_text(expr+'\n')
        ref=expr.replace(name, ('scoped_reference' if 'Scoped' in name else 'reference')+('_b' if name.endswith('_b') else ''),1)
        text=IMPORTS+REFERENCE+'\nSection Workload.\n'+context+'\n'
        order=[]
        for rep in range(args.repeat):
            for variant,body in ([('guarded',ref),('context',expr)] if rep%2==0 else [('context',expr),('guarded',ref)]):
                label=f'{variant}_{rep+1}'
                text+=f'Lemma {label} : {body} = true.\nProof.\n'
                text+=f'Profile "{d/label}" Time vm_compute.\nreflexivity.\nTime Qed.\n'
                text+=f'Print Assumptions {label}.\n'
                order.append(label)
        text+='End Workload.\n'
        (d/'Paired.v').write_text(text)
        command=[P.WRAPPER,'dune','exec','-j2','--','rocq','c','-q',*local_flags,
                 '-I',str(P.ROOT/'_build/install/default/lib'),str(d/'Paired.v')]
        result=P.execute(command,d,args.timeout)
        log=(d/'output.log').read_text();timings=P.TIMING.findall(log)
        row={'case':case,**result,'order':order,'timings':timings,
             'expression_sha256':hashlib.sha256(expr.encode()).hexdigest()}
        rows.append(row);P.write_json(output/'results.json',rows)
        print(case,result['exit_code'],len(timings),flush=True)
        if result['exit_code']!=0 or result['timeout'] or len(timings)!=2*len(order): return 1
        audit_dir=d/'audit';audit_dir.mkdir()
        command=['python3','-B',str(P.ROOT/'tools/audit-eunoia-assumptions.py'),
                 '--import','EunoiaContextPair_'+case+'.Paired',
                 '--loadpath',str(d),'EunoiaContextPair_'+case,
                 '--output-dir',str(audit_dir)]
        for label in order: command+=['--theorem',label]
        audit=P.execute(command,audit_dir,args.timeout)
        if audit['exit_code']!=0 or audit['timeout']: return 1
    if run.snapshot()!=before: raise RuntimeError('sources changed')
    metadata['loadavg_end']=os.getloadavg()
    P.write_json(output/'metadata.json',metadata)
    return 0
if __name__=='__main__':raise SystemExit(main())
