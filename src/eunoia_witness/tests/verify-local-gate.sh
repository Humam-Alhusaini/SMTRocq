#!/usr/bin/env bash
set -euo pipefail
# No solver runs. Only copy the read-only gate and replay locally produced
# certificates through its real VM computation. All writes stay in /tmp.
repo=$(cd "$(dirname "$0")/../../.." && pwd)
gate=${1:?Usage: verify-local-gate.sh /absolute/path/to/EunoiaLocal.v}
env=/home/charles/code/friends/.toolchains/smtrocq-env
scratch=$(mktemp -d /tmp/smtrocq-witness-probe.XXXXXX)
cd "$repo"
"$env" dune build -j2 src/eunoia_witness theories/checker/MainChecker.vo
cp "$gate" "$scratch/EunoiaLocal.v"
cp src/eunoia_witness/tests/GateProbe.v "$scratch/GateProbe.v"
args=(-Q _build/default/theories SMTCoq -Q "$scratch" EunoiaWitnessProbe
      -I _build/install/default/lib)
for checker in array bva cnf euf lia spl; do
  args+=(-Q "_build/default/theories/checker/small-checkers/$checker" "SMTCoq.checker.small_checker.$checker")
done
sha256sum "$scratch/EunoiaLocal.v"
"$env" rocq c "${args[@]}" "$scratch/EunoiaLocal.v" > "$scratch/gate-assumptions.log" 2>&1
"$env" rocq c "${args[@]}" "$scratch/GateProbe.v" > "$scratch/probe.log" 2>&1 || {
  cat "$scratch/probe.log"; exit 1;
}
cat "$scratch/probe.log"
printf 'Gate replay logs: %s\n' "$scratch"
