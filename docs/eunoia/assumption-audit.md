# Comparing checker assumptions

`baseline-assumptions.txt` records the distinct qualified dependency names from
`Print Assumptions` for the existing `Euf_Checker.step_checker_correct`,
`checker_correct`, `checker_b_correct` and `checker_eq_correct`. It was captured
at base revision `c0bd765`, using the private Rocq 9.3 toolchain. Full original
output is retained at `/tmp/smtrocq-assumptions/baseline.log` on the build host.
The list consists of proof irrelevance and primitive integer declarations and
specifications. It is a comparison baseline, not permission to add assumptions.

After building the modules, audit explicitly named theorems with:

```sh
python3 tools/audit-eunoia-assumptions.py \
  --import SMTCoq.checker.MainChecker \
  --theorem Euf_Checker.checker_correct \
  --theorem Euf_Checker.checker_b_correct \
  --theorem Euf_Checker.checker_eq_correct
```

The tool invokes `smtrocq-env rocq c`, retains the source, full per-theorem
`Print Assumptions` output and compiler log in a temporary directory, and writes
`summary.json`. It exits unsuccessfully on a compiler failure, an unrecognized
output format, or any dependency name outside the baseline. Use `--output-dir`
to retain the report at a chosen path outside the repository. `--env` allows an
equivalent isolated wrapper at another location.

The baseline command above passed. A negative control importing
`Stdlib.Logic.Classical_Prop` and auditing its existing `classic` declaration
failed, correctly identifying `Classical_Prop.classic` as an additional
dependency. Reports are at `/tmp/smtrocq-assumptions-script-check/summary.json`
and `/tmp/smtrocq-assumptions-script-negative/summary.json` on the build host.
The control introduces no declarations or assumptions into SMTRocq.

For the final port audit, pass the actual integrated core soundness theorem,
concrete semantic bridge correctness theorem, and tactic checker correctness
lemma explicitly. A generic theorem parameterized by a sound gate cannot stand
in for the concrete bridge and tactic lemmas. Audit representative end-to-end
UF and LIA lemmas too, to catch proof dependencies introduced by the importer.
This script does not replace the separate diff inspection for proof holes,
new assumptions or skipped proof steps.
