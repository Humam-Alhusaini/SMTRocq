#!/usr/bin/env bash
set -euo pipefail
# Independently compile the unchanged UF suite against the built install tree
# and audit its exported theorems, with all outputs in /tmp.
repo=$(cd "$(dirname "$0")/../../.." && pwd)
env="${EUNOIA_ENV:-$repo/scripts/eunoia/env}"
scratch=$(mktemp -d /tmp/smtrocq-live-uf.XXXXXX)
cd "$repo"
printf 'Live UF evidence: %s\n' "$scratch"
"$env" dune build -j2 @install > "$scratch/build.log" 2>&1
cp unit-tests/eunoia_uf.v "$scratch/eunoia_uf.v"
installed="$repo/_build/install/default/lib"
if "$env" rocq c -I "$installed" \
    -Q "$installed/coq/user-contrib/SMTCoq" SMTCoq \
    -Q "$scratch" EunoiaUF "$scratch/eunoia_uf.v" \
    > "$scratch/compile.log" 2>&1; then
  printf 'Standalone Rocq compile: exit 0\n'
else
  status=$?
  tail -30 "$scratch/compile.log"
  exit "$status"
fi
theorems=()
while read -r theorem; do
  theorems+=(--theorem "$theorem")
done < <(sed -n 's/^[[:space:]]*Lemma \([A-Za-z0-9_]*\).*/\1/p' unit-tests/eunoia_uf.v)
python3 tools/audit-assumptions.py \
  --import EunoiaUF.eunoia_uf --loadpath "$scratch" EunoiaUF \
  "${theorems[@]}" --output-dir "$scratch/assumptions"
