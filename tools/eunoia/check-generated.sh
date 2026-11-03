#!/usr/bin/env bash
set -euo pipefail
task_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
task_env=/home/charles/code/friends/.toolchains/smtrocq-env
task_tmp="$(mktemp -d /tmp/smtrocq-eunoia.XXXXXXXX)"
if [[ "${EUNOIA_KEEP_TEST_DIR:-0}" == 1 ]]; then
  echo "Retaining validation artifacts: $task_tmp"
else
  trap 'rm -rf "$task_tmp"' EXIT
fi
cd "$task_root"
export PYTHONDONTWRITEBYTECODE=1
python3 -m unittest discover -s tools/eunoia/tests -p 'test_*.py' -v
python3 tools/eunoia/regenerate.py \
  --output "$task_tmp/CpcGenerated.v" --manifest "$task_tmp/manifest.json"
cmp theories/checker/eunoia/CpcGenerated.v "$task_tmp/CpcGenerated.v"
cmp tools/eunoia/cpc-manifest.json "$task_tmp/manifest.json"
python3 tools/eunoia/compile.py tools/eunoia/tests/Programs.eo \
  --rules require_equal guarded peel choose inspect first_match output_type \
  unused_failure lazy_branch failed_values_not_equal failure_predicates failure_ok definition_capture parallel_shadow novel_assumption guarded_assumption \
  --output "$task_tmp/TestGenerated.v" --manifest "$task_tmp/test-manifest.json"
python3 - "$task_tmp/MutatedGenerated.v" <<'PY'
import importlib.util
from pathlib import Path
import sys

spec = importlib.util.spec_from_file_location("eunoia_compiler", "tools/eunoia/compile.py")
eoc = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = eoc
spec.loader.exec_module(eoc)
compiler = eoc.Compiler(Path("tools/eunoia/tests/Programs.eo"))
decl = compiler.decls["$choice"]
# Mutate the helper's source body while preserving its name and signature.
compiler.decls["$choice"] = eoc.parse(
    '(program $choice ((F Bool) (G Bool)) :signature (Bool Bool) Bool '
    '((($choice F G) F)))', decl.path)[0]
code, _ = compiler.compile(["choose"])
Path(sys.argv[1]).write_text(code)
PY
python3 tools/eunoia/replay_fixtures.py tools/eunoia/tests/fixtures/uf*.cpc \
  --output "$task_tmp/FixtureTests.v"
python3 - "$task_tmp/MutatedCpcGenerated.v" <<'PYMUT'
import sys
from pathlib import Path
sys.path.insert(0, 'tools/eunoia')
from compile import Compiler, parse
compiler = Compiler(Path('tools/eunoia/signatures/cpc/Cpc.eo'))
decl = compiler.decls['$mk_trans']
source = decl.path.read_text()
forms = parse(source.replace('(eo::requires t2 t3', '(eo::requires t2 t1'), decl.path)
compiler.decls['$mk_trans'] = next(n for n in forms if n.kind == 'list' and len(n.value) > 1 and n.value[1].value == '$mk_trans')
code, _ = compiler.compile(Path('tools/eunoia/rules.txt').read_text().split())
Path(sys.argv[1]).write_text(code)
compiler = Compiler(Path('tools/eunoia/signatures/cpc/Cpc.eo'))
decl = compiler.decls['$arith_rel_sum']
source = decl.path.read_text()
old = '(($arith_rel_sum = = a b)   (<= a b))'
assert source.count(old) == 1
forms = parse(source.replace(old, old.replace('(<= a b)', '(= a b)')), decl.path)
compiler.decls['$arith_rel_sum'] = next(n for n in forms if n.kind == 'list' and len(n.value) > 1 and n.value[1].value == '$arith_rel_sum')
code, _ = compiler.compile(Path('tools/eunoia/rules.txt').read_text().split())
Path(sys.argv[1]).with_name('LiaMutatedGenerated.v').write_text(code)
PYMUT
python3 tools/eunoia/replay_fixtures.py --scoped tools/eunoia/tests/fixtures/lia*.cpc \
  --output "$task_tmp/LiaFixtureTests.v"
python3 tools/eunoia/replay_fixtures.py --scoped tools/eunoia/tests/reduced-fixtures/*.cpc \
  --output "$task_tmp/ReducedFixtureTests.v"
cp theories/checker/eunoia/EoSyntax.v theories/checker/eunoia/EoRuntime.v \
  theories/checker/eunoia/EoArithmetic.v theories/checker/eunoia/EoOrder.v \
  tools/eunoia/tests/LiaTraceReplay.v tools/eunoia/tests/LiaRuntimeTests.v \
  tools/eunoia/tests/LiaTraceNegativeTests.v \
  tools/eunoia/tests/RuntimeTests.v tools/eunoia/tests/TraceReplay.v \
  tools/eunoia/tests/TraceNegativeTests.v "$task_tmp/"
cd "$task_tmp"
for task_module in EoSyntax EoRuntime EoArithmetic EoOrder CpcGenerated TestGenerated MutatedGenerated MutatedCpcGenerated LiaMutatedGenerated TraceReplay RuntimeTests FixtureTests TraceNegativeTests LiaTraceReplay LiaRuntimeTests LiaFixtureTests LiaTraceNegativeTests ReducedFixtureTests; do
  "$task_env" rocq compile -q -Q . SMTCoq.checker.eunoia "$task_module.v"
done
"$task_env" rocq check -silent -Q . SMTCoq.checker.eunoia \
  SMTCoq.checker.eunoia.RuntimeTests SMTCoq.checker.eunoia.FixtureTests \
  SMTCoq.checker.eunoia.TraceNegativeTests SMTCoq.checker.eunoia.LiaRuntimeTests \
  SMTCoq.checker.eunoia.LiaFixtureTests SMTCoq.checker.eunoia.LiaTraceNegativeTests \
  SMTCoq.checker.eunoia.ReducedFixtureTests
