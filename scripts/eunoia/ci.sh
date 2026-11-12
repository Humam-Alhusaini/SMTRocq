#!/bin/sh
set -eu
cd "$(dirname "$0")/../.."
if [ ! -f external/rocq-eunoia-checker/theories/checker/eunoia/EunoiaCertificate.v ]; then
  echo 'Initialize the checker dependency: git submodule update --init --recursive' >&2
  exit 1
fi
python3 -B scripts/eunoia/install_toolchain.py
dune build --ignore-promoted-rules -j 2 theories \
  unit-tests/smtrocq.vo unit-tests/smtrocq_compatibility.vo unit-tests/eunoia_tactics.vo unit-tests/eunoia_uf.vo \
  unit-tests/eunoia_uf_bool.vo unit-tests/eunoia_lia.vo \
  unit-tests/eunoia_purification.vo unit-tests/eunoia_integer_casts.vo unit-tests/eunoia_division.vo \
  tools/kernel-acceptance-probe/Controls.vo
dune runtest --ignore-promoted-rules -j 2 \
  src/eunoia src/eunoia_backend src/eunoia_witness \
  scripts/eunoia benchmarks/eunoia
python3 -B scripts/eunoia/check_modes.py
python3 -B scripts/eunoia/check_proofs.py
