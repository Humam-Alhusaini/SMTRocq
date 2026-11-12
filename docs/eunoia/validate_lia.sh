#!/usr/bin/env bash
# Isolated validation until the coordinator registers the eunoia dune theory.
set -euo pipefail
cd "$(dirname "$0")/../.."
env_wrapper=/home/charles/code/friends/.toolchains/smtrocq-env
validation_dir=${1:-$(mktemp -d /tmp/smtrocq-lia-validation.XXXXXX)}
mkdir -p "$validation_dir"
validation_dir=$(realpath "$validation_dir")

"$env_wrapper" dune build theories > "$validation_dir/dune-build.log" 2>&1
load_paths=(
  -Q _build/default/theories/utils SMTCoq.utils
  -Q _build/default/theories/structures SMTCoq.structures
  -Q _build/default/theories/checker/fol SMTCoq.checker.fol
  -Q _build/default/theories/checker/small-checkers/euf SMTCoq.checker.small_checker.euf
  -Q _build/default/theories/checker/small-checkers/lia SMTCoq.checker.small_checker.lia
  -Q "$validation_dir" SMTCoq.checker.eunoia
)
for module in EunoiaLia EunoiaLiaTests; do
  cp "theories/checker/eunoia/$module.v" "$validation_dir/$module.v"
  "$env_wrapper" rocq c "${load_paths[@]}" "$validation_dir/$module.v" \
    > "$validation_dir/$module.log" 2>&1
done

cat > "$validation_dir/LiaBaselineAssumptions.v" <<'EOF'
From Stdlib Require Import Bool List Uint63 ZMicromega.
From SMTCoq.utils Require Import Misc PArray.
From SMTCoq.checker.fol Require Import State Terms.
From SMTCoq.checker.small_checker.lia Require Import LIA.
Print Assumptions LIA.valid_check_micromega.
EOF
"$env_wrapper" rocq c "${load_paths[@]}" "$validation_dir/LiaBaselineAssumptions.v" \
  > "$validation_dir/LiaBaselineAssumptions.log" 2>&1

python3 - "$validation_dir" <<'PY'
from pathlib import Path
import re
import sys

root = Path(sys.argv[1])
# Print Assumptions uses an unindented name followed by ':' for each entry.
def dependencies(text):
    return set(re.findall(r"^([\w.]+)\s*:", text, flags=re.MULTILINE))

baseline = dependencies((root / "LiaBaselineAssumptions.log").read_text())
bridge = (root / "EunoiaLia.log").read_text().split("Axioms:")[1:]
assert len(bridge) == 4, "Expected all four bridge assumption audits"
for index, block in enumerate(bridge, 1):
    additions = dependencies(block) - baseline
    assert not additions, f"Bridge audit {index} adds dependencies: {additions}"
print("Four Print Assumptions audits: no dependencies beyond existing LIA soundness")
PY

"$env_wrapper" rocq check "${load_paths[@]}" \
  SMTCoq.checker.eunoia.EunoiaLiaTests > "$validation_dir/kernel-check.log" 2>&1
printf 'Bridge, 13 examples, and kernel recheck passed; logs: %s\n' "$validation_dir"
