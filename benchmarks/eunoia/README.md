# Checked tactic benchmarks for the Eunoia port

This harness runs the existing checked `verit` and `cvc4` tactics on the same
small UF/LIA goals. It also invokes the checked `cvc5_eunoia` and `smtrocq`
tactics when selected explicitly. `smtrocq` checks compiled semantic
certificates; `cvc5_eunoia` also validates signature-generated CPC source
conformance. Coverage is still bounded. The default
benchmark runs only the existing backends. There is no
solver-only benchmark or external-prover performance claim here.

## Reproduce

From the repository root, using an activated Rocq/OCaml toolchain (see
[setup](../../scripts/eunoia/README.md)):

```sh
python3 -B -m unittest discover -s benchmarks/eunoia -p test_run.py -v
python3 benchmarks/eunoia/run.py --backends verit cvc4 --repeat 3 --timeout 30 --jobs 2
```

The runner prints a fresh `/tmp/smtrocq-eunoia-*` results directory. It invokes
`scripts/eunoia/env dune build -j2 theories` first,
with a 900-second build timeout, and runs cases serially. All Rocq, OCaml, Dune,
and solver discovery goes through that wrapper. No installation, system changes,
shared Dune edits, or server is needed. Python uses only its standard library.
`--wrapper PATH` selects another explicitly provisioned environment;
`--output /absolute/new/directory` sets the artifact directory (it must not
already exist). `--skip-build` is only for a previously successful build in the
same checkout. The harness derives logical load paths from existing theory
stanzas rather than adding a benchmark stanza to shared files.
`--cases PATH` selects a JSON workload manifest for a focused diagnostic run;
the exact manifest, its source path and hash are retained with the results.
Compare backends on the same selected manifest.
`--entrypoint SMTRocq` uses the lean public import for every selected backend;
the default remains the original full `SMTCoq` import. Use the same entry point
for a matched comparison.
`integer-cuts.json` is a separate extension with 12 positive integer-cut/mixed-UF
goals and five explicit false controls. `scalability.json` adds 21 positive diagnostics: Boolean/propositional equality
chains, nested congruences, coefficient cuts/parity, mixed UF cuts and inequality
cycles. Its outcomes remain separate from the original regression workload.
`division.json` separately exercises proved facts about Rocq integer division
and modulo, including negative/zero divisors and false controls. See
[the semantic scope](../../docs/eunoia/division.md); baseline tactics do not
receive Eunoia's automatically proved facts. `known-values.json` adds five
positive equality-guided evaluations and three false controls; it does not
change the division checkpoint's 35-case manifest.
`helper-cache.json` is a separate seven-case matched diagnostic for the
experimental `EUNOIA_HELPER_CACHE=0|1` paths; it copies existing UF, arithmetic,
division and scalability cases without changing their statements or timeout.
The original 20-case manifest is retained
unchanged, so historical solved counts remain comparable.
`EUNOIA_CVC5_PROFILE` is recorded in metadata when comparing fixed solver profiles.

To exercise the integrated tactic:

```sh
python3 benchmarks/eunoia/run.py --entrypoint SMTRocq \
  --backends verit cvc5_eunoia smtrocq --repeat 4 --timeout 30 --jobs 2
```

A preflight imports the requested modules and resolves each actual tactic name
without invoking a solver. Missing tactics/imports are recorded as `unavailable`,
with null timing fields and no solved attempts; no fallback tactic is used.
A `cvc5` on PATH may be distinct from the pinned 1.4.2 executable
selected by the new backend. The ordinary PATH probe records the older binary
and its hash. When either `cvc5_eunoia` or `smtrocq` is selected, the harness additionally runs
`scripts/eunoia/verify_toolchain.py`, which verifies the cached 1.4.2 binary,
archives and matching signature files and reports their exact paths, hashes and
version. Failure ends the benchmark with status 2. Metadata also records the
backend solver source hash, so its fixed executable selection is reviewable.
A CPC-producing executable alone is insufficient for this benchmark.

Exit status is `0` if every positive attempt was checked and every negative
control was rejected, `1` for backend errors, timeouts, unavailable backends,
unreadable timing output, or unexpected negative successes, and `2` if the
initial build failed. Invalid CLI arguments also return `2`. Backend coverage
gaps therefore produce useful results and exit `1`; examine their logs.

## Workload and success boundary

`cases.json` has six positive UF-shaped goals over integers, six positive
abstract-carrier UF goals, six positive LIA goals, and two
negative controls. Sources point to the corresponding blocks in
the existing and Eunoia integration tests. Goals mix propositional and Boolean
presentation, as the existing tests do. The integer UF cases use equality and
uninterpreted functions or predicates without arithmetic operations, but solver
logic selection may still include LIA and trigger arithmetic normalization.
The abstract-carrier goals quantify `A : Type` with `HA : CompDec A`, and include
chains, binary functions, predicates, disjunctive roots and two distinct sorts.
These exercise proof-local carrier universes as well as genuine QF_UF solver
problems. The suite is a regression-sized
sample, not a representative difficulty distribution.

Each attempt starts a new compiler process and calls exactly the named tactic.
No auxiliary proof tactic completes remaining obligations. A positive counts
as solved only when compilation exits zero, `Qed` has succeeded, a fresh `.vo`
exists, both timing messages parse, and the final marker after
`Print Assumptions EunoiaBenchmark.bench_result` appears. The assumption report
must parse and contain only names in the existing checker baseline. Unknown
dependencies produce `unsupported_assumptions`; an unrecognized report produces
`assumption_error`. Neither counts as solved. This matters because `cvc4` can return
remaining obligations. It is not enough for a solver to report unsatisfiability
or for the tactic command itself to succeed. The generated files use the
selected public import and the named checked tactic. Their imports are local to a
module that closes before printing assumptions, preserving qualified dependency
names. Both the baseline and its parser are hashed in the run metadata.

The false controls assert injectivity of an arbitrary function and a strict
integer gap from a non-strict inequality. Concrete counterexamples are in the
manifest. They are attempted directly and expected to fail compilation.
`negative_rejected` means failure after entering the tactic and before the
successful proof marker; it does not distinguish a semantic rejection from an
internal tactic error. Parser/import failures before invocation are `error`;
timeouts are always `timeout`. All diagnostics are retained. Negative attempts
are excluded from all positive solved counts and timing aggregates, even if
they unexpectedly compile. An unexpected success fails the run.

No soundness lemma is added by the harness. Every successfully generated
benchmark theorem is audited with `Print Assumptions`, whose complete output
and parsed dependency names are retained. The allowed names are fixed by
`docs/eunoia/baseline-assumptions.txt`. Existing SMTCoq/Rocq assumptions (including primitive
integer operations/specifications and proof irrelevance where used) are not removed
or claimed absent by this benchmark.

## Timing and retained evidence

* `tactic_wall_s` is Rocq's `Time backend` elapsed wall time, including frontend
  preprocessing, external solver interaction, proof translation, and the checked
  tactic's computation. It excludes imports and `Qed`; it is **not** solver-only
  time. User/system CPU fields are separate and do not replace wall time.
* `qed_wall_s` is the following `Time Qed` transaction, retained separately so
  deferred kernel work is visible. A rejected proof never enters solved totals.
* `process_wall_s` uses Python's monotonic clock around the whole command. It
  includes the environment wrapper, Dune, Rocq startup, imports, tactic, `Qed`,
  assumptions audit, and output. It must not be called tactic time.

Rocq reports rounded times (typically milliseconds); zero is possible for short
transactions. Backend order reverses every other repeat; each case/repeat uses
a fresh working artifact directory and `TMPDIR`. There are no solver warmups;
the import/name preflight occurs once per backend. File caches and machine load
can still affect results. This runner does not clear OS caches or constrain
other jobs. The timeout covers the whole per-case compiler process, not just
the solver. On expiration the compiler process group is killed. On Linux with
pidfd support, cleanup also pins and kills observed descendants that started a
separate session, as the cvc5 runner does. Python's native pidfd APIs or libc's
equivalent APIs provide this support; other hosts only get process-group cleanup.
The timeout tests exercise both ordinary and detached solver children. Descendant
discovery uses a snapshot at expiration, so this is not a process sandbox.
Metadata records CPU count, initial load averages and the witness/table/Rocq profiling flags;
each attempt retains UTC start/end timestamps and load averages before/after it.
These observations help identify concurrent load, but do not control it.

Artifacts are outside Git by default:

* `metadata.json`: branch, commit, dirty status/diff, workload and harness hashes,
  exact invocation, wrapper hash, tool versions, resolved executable paths and
  hashes, and relevant private-toolchain environment variables.
* `build/`, `metadata/`, `preflight/`: exact argument arrays, working directories,
  exit codes, timeouts, process wall times, and combined stdout/stderr logs.
* `runs/BACKEND/CASE/REPEAT/`: generated `case.v`, checked `.vo` on success,
  `command.json`, `output.log`, and private temporary files. To replay, use the
  argument array and working directory in `command.json`; use a new artifact
  directory for another measured run.
* `attempts.jsonl`: append-only per-attempt records, also useful if interrupted.
* `results.json`, `results.csv`: all attempts, including failures, controls,
  and unavailability. Failed tactic transaction times are retained when Rocq
  emitted them. JSON includes the summary; CSV contains individual attempts.
* `summary.json`: unique positive cases, scheduled and executed positive
  attempts, solved attempts, cases solved in **every** repeat, per-theory solved
  counts, status counts, and successful-attempt timing aggregates.

Successful timing totals/medians have different denominators if backend solved
sets differ. Compare per-case rows on a common solved set for latency analysis;
do not use aggregate sums to rank backend speed. No published comparative claim
is justified by these small local measurements alone.

Generate a Markdown results table from one run with:

```sh
python3 benchmarks/eunoia/report.py /path/to/results.json
```

The first table reports positive coverage and false-control rejection separately.
A second table compares each backend pair only on matching case/repeat attempts
that both checked. It reports no latency when that shared set is empty. Duplicate
attempts, inconsistent solved flags and invalid successful timings reject rather
than silently inflating a denominator. The report consumes one run and does not
combine differently configured workloads or revisions.

The metadata probe checks local availability of `lean`, `lake`, and `isabelle`
on the private wrapped PATH. In the initial environment all three resolved to
null. There is consequently no locally runnable Lean-SMT or Sledgehammer
baseline in that environment; this PATH observation is not a machine-wide
installation audit. No large toolchains were installed, and no performance
comparison to those systems is asserted.

## Producer cache ablations

Set `EUNOIA_ENV` to an optional activated-toolchain wrapper; otherwise the
repository's `scripts/eunoia/env` uses the caller's PATH. Install pinned cvc5
with `python3 scripts/eunoia/install_toolchain.py` before measurement.

`EUNOIA_DISABLE_TERM_CACHE=1`, `EUNOIA_DISABLE_DERIVE_CACHE=1`, and
`EUNOIA_DISABLE_WITNESS_CACHE=1` disable only untrusted producer sharing. Both
variants retain the same generated and semantic checking, `Qed`, assumption
audits, negative controls, and timeout boundaries. Switch values appear in the
metadata. Source and installed proof/plugin fingerprints must remain unchanged
throughout each run; the report rejects a run with failed integrity.

Compare the same cases and repeats, run variants serially on an idle machine,
and retain failures and timeouts in the denominator. These switches do not
remove trusted checker work and do not establish competitiveness by themselves.

For an isolated comparison of verified certificate sharing, leave the producer
caches unchanged and compare the default with `EUNOIA_DISABLE_CHECKED_CACHE=1`.
The latter selects the original checked wrappers. `EUNOIA_CACHE_PROFILE=1` logs
source-step/shared-certificate counts in both variants. The same source rules,
typing, syntax binding, scope/liveness checks and kernel acceptance apply.

## Checked-certificate cache experiments

The default backend selects checked sharing adaptively from exact certificate
repetition. `EUNOIA_FORCE_CHECKED_CACHE=1` forces the proved shared representation;
`EUNOIA_DISABLE_CHECKED_CACHE=1` forces the reference representation and takes
precedence. `EUNOIA_CACHE_PROFILE=1` records selection and repetition counts.
The result metadata records these flags plus the three producer-cache switches.
Compare runs only with identical source/artifact fingerprints, workload and
compiler. A changed fingerprint invalidates a run.

A two-repeat, five-positive/two-negative matched experiment on commit `9f31bb6`
found no repeated certificates in those cases. Forced sharing was approximately
neutral on four cases and slower on the smallest UF case (median tactic time
1.826 s reference versus 2.298 s shared). This motivated the adaptive default;
it does not establish a shared-checker speedup.

## Source-evaluator experiments

The metadata also records `EUNOIA_DECLARED_CONCLUSIONS`,
`EUNOIA_HELPER_CACHE`, `EUNOIA_PROGRAM_INDEX`, and `EUNOIA_STAGED_PROGRAMS`.
Printed conclusions default to enabled; the other three default to disabled.
Set every switch explicitly in matched experiments. Helper-cache mode takes precedence over direct compilation, followed by
staged evaluation and then the program index.
The isolated checker repository supplies separate component runners; their
results do not measure the complete tactic.

For the specialized evaluator, alternate `EUNOIA_STAGED_PROGRAMS=0|1` while
keeping printed conclusions enabled and the helper cache and program index
disabled. Use identical frozen sources and installed proof/plugin artifacts,
retain failures and false controls, and preserve the whole-compiler timeout.

`EUNOIA_DIRECT_PROGRAMS=1` tests direct signature-program compilation while
preserving normal adaptive sharing. Set it explicitly to `0` in experiments on
other optimizations. Its normal, forced-shared and forced-reference native
replays are available through `scripts/eunoia/check_modes.py`.

`EUNOIA_MODEL_DAG=auto` (the default) shares model encodings for roots with at
least 16 nested applications. Compare it with `=0` using `--cases
benchmarks/eunoia/model-graph.json`; `=1` forces it even on small goals. This
changes the adapter's encoding work while retaining the full signature-generated
source checker. [Design and matched results](../../docs/eunoia/indexed-model-encoding.md)
document the exact refinement, fallback and remaining veriT gap.

## Current compiled tactic checkpoint

The [verified `smtrocq` guide](../../docs/eunoia/smtrocq-tactic-2026-11-11.md)
reports the frozen four-round comparison and separate scaling/coverage runs.
It includes unfavorable results and whole-compiler timing, which remains about
5% slower than veriT despite the faster tactic-plus-`Qed` measurements.
Metadata records the checking contracts and effective compact-theory defaults.
The exact source/native/proof fingerprint must remain unchanged within each run.

The [November 12 coverage extension](../../docs/eunoia/array-integer-coverage-2026-11-12.md)
adds separate `arrays.json` and `integer-operations.json` manifests with actual
Rocq array/integer semantics and false-goal controls. Array runs require
`--extra-import SMTCoq.structures.FArray`. Keep those extensions separate from
the standard UF/LIA speed comparison; a backend's missing operation semantics
is a coverage failure, not a successful timed result.
