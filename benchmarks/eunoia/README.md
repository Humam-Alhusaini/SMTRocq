# Checked tactic benchmarks for the Eunoia port

This harness runs the existing checked `verit` and `cvc4` tactics on the same
small UF/LIA goals. It also invokes the integrated checked `cvc5_eunoia` tactic
when selected explicitly. Its coverage is still under development. The default
benchmark runs only the existing backends. There is no
solver-only benchmark or external-prover performance claim here.

## Reproduce

From the repository root, using the private toolchain:

```sh
python3 -B -m unittest discover -s benchmarks/eunoia -p test_run.py -v
python3 benchmarks/eunoia/run.py --backends verit cvc4 --repeat 3 --timeout 30 --jobs 2
```

The runner prints a fresh `/tmp/smtrocq-eunoia-*` results directory. It invokes
`/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2 theories` first,
with a 900-second build timeout, and runs cases serially. All Rocq, OCaml, Dune,
and solver discovery goes through that wrapper. No installation, system changes,
shared Dune edits, or server is needed. Python uses only its standard library.
`--wrapper PATH` selects another explicitly provisioned environment;
`--output /absolute/new/directory` sets the artifact directory (it must not
already exist). `--skip-build` is only for a previously successful build in the
same checkout. The harness derives logical load paths from existing theory
stanzas rather than adding a benchmark stanza to shared files.

To exercise the integrated tactic:

```sh
python3 benchmarks/eunoia/run.py --backends verit cvc4 cvc5_eunoia --repeat 3 --timeout 30 --jobs 2
# If integration exports it from a separate module, append:
# --extra-import SMTCoq.ACTUAL_MODULE_NAME
```

A preflight imports the requested modules and resolves each actual tactic name
without invoking a solver. Missing tactics/imports are recorded as `unavailable`,
with null timing fields and no solved attempts; no fallback tactic is used.
The private wrapper's `cvc5` on PATH is distinct from the pinned 1.4.2 executable
selected by the new backend. The ordinary PATH probe records the older binary
and its hash. When `cvc5_eunoia` is selected, the harness additionally runs
`scripts/eunoia/verify_toolchain.py`, which verifies the private 1.4.2 binary,
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

`cases.json` has six positive UF-shaped goals, six positive LIA goals, and two
negative controls. Sources point to the corresponding blocks in
`unit-tests/verit_tactics.v`. Goals mix propositional and Boolean presentation,
as the existing tests do. UF cases use equality and uninterpreted functions or
predicates over `Z`, without arithmetic operations. These are UF-shaped goals
over a fixed integer carrier, not a test of arbitrary uninterpreted sorts;
solver logic selection may still include LIA. The suite is a regression-sized
sample, not a representative difficulty distribution.

Each attempt starts a new compiler process and calls exactly the named tactic.
No auxiliary proof tactic completes remaining obligations. A positive counts
as solved only when compilation exits zero, `Qed` has succeeded, a fresh `.vo`
exists, both timing messages parse, and the final marker after
`Print Assumptions bench_result` appears. This matters because `cvc4` can return
remaining obligations. It is not enough for a solver to report unsatisfiability
or for the tactic command itself to succeed. The generated files use the
existing SMTCoq import and proof-checking path.

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
is retained in its log. Existing SMTCoq/Rocq assumptions (including primitive
integer/array specifications and proof irrelevance where used) are not removed
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
the solver; on expiration the entire process group is killed, including solver
children. The safety test exercises that behavior with a child process.

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

The metadata probe checks local availability of `lean`, `lake`, and `isabelle`
on the private wrapped PATH. In the initial environment all three resolved to
null. There is consequently no locally runnable Lean-SMT or Sledgehammer
baseline in that environment; this PATH observation is not a machine-wide
installation audit. No large toolchains were installed, and no performance
comparison to those systems is asserted.
