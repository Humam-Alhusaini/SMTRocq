#!/usr/bin/env python3
"""Audit named computation examples and their new runtime/query entry points."""
from pathlib import Path
import json
import re
import subprocess
import sys

root = Path(__file__).resolve().parents[3]
artifacts = Path(sys.argv[1]).resolve()
names = []
for module, path in [('IntegerCastTests', root / 'tools/eunoia/tests/IntegerCastTests.v'),
                     ('IntegerFixtureTests', artifacts / 'IntegerFixtureTests.v')]:
    names += [module + '.' + n for n in re.findall(r'^Example (\w+)', path.read_text(), re.M)]
names += ['EoRuntime.application_hints_with_polymorphic',
          'EoRuntime.collect_application_hints_with_polymorphic',
          'EoRuntime.run_rule_assuming_with_nils_polymorphic',
          'EoRuntime.run_surface_rule_assuming_with_nils_polymorphic',
          'CpcGenerated.derive', 'CpcGenerated.derive_assuming',
          'LiaTraceReplay.lia_query', 'LiaTraceReplay.trace_final_with']
source = ['From Stdlib Require Import String.',
          'From SMTCoq.checker.eunoia Require Import IntegerCastTests IntegerFixtureTests.',
          'Open Scope string_scope.']
for name in names:
    source += [f'Eval compute in "audit:{name}".', f'Print Assumptions {name}.']
(artifacts / 'IntegerAssumptionAudit.v').write_text('\n'.join(source) + '\n')
command = ['/home/charles/code/friends/.toolchains/smtrocq-env', 'rocq', 'compile',
           '-q', '-Q', '.', 'SMTCoq.checker.eunoia', 'IntegerAssumptionAudit.v']
proc = subprocess.run(command, cwd=artifacts, text=True, capture_output=True)
output = proc.stdout + proc.stderr
(artifacts / 'integer-assumptions.log').write_text(output)
assert proc.returncode == 0, output
blocks = re.split(r'\s*= "audit:([^"\n]+)"\s*: string\s*', output)
assert not blocks[0].strip(), blocks[0]
results = {blocks[i]: blocks[i+1].strip() for i in range(1, len(blocks), 2)}
assert list(results) == names, results
assert all(value == 'Closed under the global context' for value in results.values()), results
(artifacts / 'integer-assumptions.json').write_text(json.dumps(results, indent=2) + '\n')
print(f'{len(results)}/{len(names)} named declarations closed under the global context')
