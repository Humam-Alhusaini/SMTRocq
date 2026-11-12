# SMTRocq tactic benchmarks

These benchmarks measure end-to-end Rocq tactics, including preprocessing,
solver execution, translation, verified certificate checking, and `Qed`.
They do not isolate the Eunoia checker. Solver-free checker benchmarks live in
[rocq-eunoia-checker](https://github.com/Humam-Alhusaini/rocq-eunoia-checker).
The directory name refers to CVC5's proof format, not ownership of a checker.

Initialize the submodule, install the pinned solver, and build before timing:

```sh
git submodule update --init --recursive
python3 -B scripts/eunoia/install_toolchain.py
dune build -j2 @install
python3 -B benchmarks/eunoia/run.py --skip-build --entrypoint SMTRocq \
  --backends verit smtrocq --repeat 3 --timeout 30 --output /tmp/smtrocq-timing
python3 -B benchmarks/eunoia/report.py /tmp/smtrocq-timing/results.json
```

Install veriT for a comparison. A missing backend, failed proof, timeout, or
false-goal acceptance remains a failure in the results; it is not a successful
latency sample. `cases.json` contains twelve UF and six LIA goals plus two
false-goal controls. Other JSON manifests cover scaling, integer cuts,
division/modulo, and known values. Select one with `--cases`.

The runner retains each exact statement, command, output, assumption report,
whole-compiler deadline, and separate tactic/`Qed` timings. It alternates backend
order, serializes solver runs, verifies the pinned CVC5 binary/signatures, and
rejects runs if checker sources or installed proof/plugin fingerprints change.
Fingerprints include the pinned external checker. Do not time concurrently with
builds, tests, audits, or another benchmark process.

`smtrocq` checks semantic certificates for the actual theorem.
`cvc5_eunoia` additionally validates CPC source conformance and should be labeled
as that separate contract when measured. Neither is a solver-only timing.
Compiler startup, imports, and final file processing are reported separately
from tactic plus `Qed`; do not present one measurement boundary as the other.

The [November 11 report](../../docs/benchmarks/smtrocq-tactic-2026-11-11.md)
contains the previous frozen comparison, including unfavorable outcomes. Its
JSON evidence is retained unchanged and predates the repository split. No new
performance result is claimed for a structural cleanup.
