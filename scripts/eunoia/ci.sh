#!/bin/sh
set -eu
cd "$(dirname "$0")/../.."
python3 -B scripts/eunoia/install_toolchain.py
dune build --ignore-promoted-rules -j 2 theories \
  unit-tests/eunoia_tactics.vo unit-tests/eunoia_uf.vo \
  unit-tests/eunoia_uf_bool.vo unit-tests/eunoia_lia.vo \
  unit-tests/eunoia_purification.vo unit-tests/eunoia_integer_casts.vo unit-tests/eunoia_division.vo \
  tools/eunoia-kernel-acceptance-probe/Controls.vo
dune runtest --ignore-promoted-rules -j 2 \
  src/eunoia src/eunoia_backend src/eunoia_witness \
  tools/eunoia tools/eunoia-runtime-profile scripts/eunoia benchmarks/eunoia
python3 -B scripts/eunoia/check_modes.py
python3 -B scripts/eunoia/check_proofs.py
