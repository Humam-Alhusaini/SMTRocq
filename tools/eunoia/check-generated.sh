#!/usr/bin/env bash
set -euo pipefail
task_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
task_env=/home/charles/code/friends/.toolchains/smtrocq-env
task_tmp="$(mktemp -d /tmp/smtrocq-eunoia.XXXXXXXX)"
trap 'rm -rf "$task_tmp"' EXIT
cd "$task_root"
export PYTHONDONTWRITEBYTECODE=1
python3 -m unittest discover -s tools/eunoia/tests -p 'test_*.py' -v
python3 tools/eunoia/compile.py tools/eunoia/signatures/Initial.eo \
  --rules refl symm true_intro true_elim false_intro false_elim eq_resolve \
  modus_ponens not_not_elim contra eq-refl eq-symm ite_eq \
  --output "$task_tmp/CpcGenerated.v" --manifest "$task_tmp/manifest.json"
cmp theories/checker/eunoia/CpcGenerated.v "$task_tmp/CpcGenerated.v"
python3 tools/eunoia/compile.py tools/eunoia/tests/Programs.eo \
  --rules require_equal guarded peel choose inspect first_match output_type \
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
cp theories/checker/eunoia/EoSyntax.v theories/checker/eunoia/EoRuntime.v \
  tools/eunoia/tests/RuntimeTests.v "$task_tmp/"
cd "$task_tmp"
for task_module in EoSyntax EoRuntime CpcGenerated TestGenerated MutatedGenerated RuntimeTests; do
  "$task_env" rocq compile -q -Q . SMTCoq.checker.eunoia "$task_module.v"
done
"$task_env" rocq check -silent -Q . SMTCoq.checker.eunoia SMTCoq.checker.eunoia.RuntimeTests
