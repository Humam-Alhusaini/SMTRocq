# Checked-context validation experiment

This is a local implementation experiment in the cvc5/Eunoia port. It does not
establish overall port completion or competitive performance.

The experiment compares the existing whole checker against callbacks using an
explicitly prechecked immutable table context. It must keep standalone `eval`,
`scope_eval`, `typeof` and `gate` rejection behavior. One checked top-level
`tables_wf` on exactly the same tables is mandatory; neither the source nor the
witness supplies a trusted readiness flag. All generated-rule derivations,
ordered root and premise bindings, pushed assumptions, local command results,
bounds/type checks, freshness/live-reference checks, fallback rejections,
unused steps and final empty-clause checks are retained.

The original guard hoists (`26da5ad`, `3732a17`) are already in the baseline.
`PArray` is the existing pure AVL-map implementation. No array extensionality
or native-array assumptions are needed for pointwise callback refinement.

## Reproduction and measurement boundaries

Run from the repository root with the private toolchain. The new driver reuses
`tools/eunoia-profile/run.py`, replacing its workload list with five live public
tactic goals: abstract-carrier UF congruence, predicate transport, contradictory
integer bounds, nontrivial coefficient normalization, and scoped integer
comparison. The arithmetic replay is not used as a timing workload. Fuel,
capacity production, solver flags and all semantic operations are unchanged.

```sh
/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2 @install
ROCQ_PROFILE_COMPONENTS=-unification python3 -B tools/eunoia-context-profile/run.py \
  --output /tmp/smtrocq-context/runtime-before --repeat 2 --timeout 180 --controls
```

Each fresh compiler runs `Time cvc5_eunoia`, `Time Qed`, then `Print Assumptions`.
The existing qualified-name auditor checks each exported theorem against the
existing 52-entry baseline. Raw transaction wall/user/system times are retained
in `CASE-REPETITION/output.log`; command, exit, source, artifact and load records
are adjacent. Native `vm_conv` events delimit final checked conversion. These
inclusive native events overlap other timings and must not be added. Compiler
process wall time includes startup, imports, profile output and Dune overhead.
Measurements run on a shared, uncontrolled machine; small differences are not
an efficiency claim. The profile timeout does not alter production evaluator
fuel or the private solver's flags.

An initial baseline was collected on `46c461f8b460de8b9b18d3519f5ef83961794a99`
at `/tmp/smtrocq-context/before`. It is retained separately from the matching
runtime comparison. The child then fast-forwarded to the explicitly authorized
`41c93f5` parent dependency. Both sides of the final context comparison use that
same runtime implementation; dependency first-argument sharing is not attributed
to context validation.

## Proof design of the trial

The trial factors the original guarded evaluator and local gate through helper
callbacks accepting a readiness Boolean and, for rule evaluation, a type query.
The standalone definitions supply exactly their original computed guards. The
whole tactic supplies `true` and the unguarded `syntax_typeof` only behind its
mandatory global `tables_wf` acceptance prerequisite. The generated evaluator
remains `CpcGenerated.derive` / `derive_with` / `derive_assuming_with`.

Pointwise lemmas prove equality of each callback under `tables_wf = true`.
That Boolean entails the exact names, formula, atom and atom-typing predicates
on the same immutable tables. Generic equality lemmas propagate pointwise
callback equality through `check_step`, ordinary `run`, scoped `close` and
scoped `run`, then their respective Boolean checkers. They do not change those
machines or traces. The two final `checker_guarded_refine` lemmas quantify all
tables, names, fuel, capacity, roots, root terms, claims, traces and final slots
(and the scoped primitive hook); they have **no validity hypothesis**. The
invalid-table branch returns the same false Boolean; the valid branch applies
the pointwise lemmas. No functional extensionality is used.

The main soundness wrappers transport acceptance to the original concrete
checker correctness proofs, using existing State/Atom/Form and EUF/LIA results.
The public tactic never asks a caller or source certificate for trusted table
validity. The 13 new trial refinement lemmas passed the qualified assumption
auditor in `/tmp/smtrocq-context/refinement-assumptions/summary.json` (compiler
exit 0, no added assumptions). These reports are relative to the established
baseline: native integer and existing proof-irrelevance dependencies remain;
this is not a claim that every refinement lemma is globally axiom-free.

`EunoiaContextTests.v` supplies concrete scoped positives and malformed-table,
root, reference, certificate, unused-step and final-result controls. Its
standalone evaluator, scope evaluator and local-gate controls ensure the
external rejection contracts are preserved. All examples include
`Print Assumptions`. The first trial build exited 1 because the new tests
needed an explicit `@` for the scoped API's implicit table parameter; after
that test-only correction, the controls build exited 0. The production
refinement proofs compiled in that first build.

The fresh-process public timings do not establish a broad improvement: the
normalization VM boundary decreased in those two rounds, but UF, scoped and
`Qed` results are mixed. `tools/eunoia-context-profile/paired.py` therefore
extracts the complete checker expression from `Print` of an already accepted
public proof, records its SHA-256, and compiles guarded/context lemmas with
**identical** table, fuel, source-trace, capacity, root and certificate arguments.
It alternates their order across three rounds in one compiler process. Each
lemma recomputes the whole checker, proves equality to true, closes with `Qed`,
and prints assumptions; each is also passed through the qualified auditor.
It does not reuse the accepted Boolean result or skip solver-source steps.
Only solver and witness *production* are outside this paired conversion probe.
A truncated printed expression fails closed, as do unsupported entry points,
compiler failures, missing timing rows and failed assumption audits.

The first paired-tool smoke failed because congruence uses `checker`, not
`checker_b`; the second failed because the default printing depth inserted
ellipsis. The tool now supports the actual `checker`/`checker_b` entry points,
sets a sufficient printing depth, and rejects ellipsis explicitly. The corrected
smoke passed. Smoke timings overlap regression compilation and are excluded
from the measurement conclusion.

## Result: do not integrate the fast path

The production trial is **not retained**. The existing hoisted definitions already put immutable guards outside their
changing per-step arguments. The trial removes additional
copies of table/name checking, but these measurements do not establish useful,
reproducible whole-tactic savings worth adding six-module production complexity.
They do not establish that validation costs zero or rule out a larger workload.

[The retained measurements](../../tools/eunoia-context-profile/measurements.json)
contain **all** 20 fresh-process wall/user/system transaction rows and 30 paired
compute/Qed rows, exact expression hashes and machine load records. Unaggregated
commands, profiles, compiler logs and proofs remain under
`/tmp/smtrocq-context/`. The two fresh-process rounds each checked all five
public goals and the three existing control groups; all per-goal and control
audits exited 0. Both measured source snapshots remained unchanged during their
runs. Runtime source SHA-256 on both sides was
`ad77b97b9717c1b6f9add760c3f338389bdc419ee815725ed4d575e3bd8fa4d4`.

Exact-input pairs, median **user CPU seconds** across three alternating rounds:

| Actual public workload | Guarded compute | Context compute | Guarded Qed | Context Qed |
| --- | ---: | ---: | ---: | ---: |
| UF congruence | 0.988 | 1.036 | 1.015 | 0.911 |
| UF predicate | 0.320 | 0.328 | 0.426 | 0.338 |
| LIA contradictory bounds | 0.359 | 0.396 | 0.425 | 0.374 |
| LIA coefficient normalization | 5.941 | 5.821 | 6.389 | 6.253 |
| LIA scoped comparison | 1.855 | 1.696 | 1.818 | 1.956 |

These small samples overlap uncontrolled load and the candidate regression
build. In particular, the fresh-process normalization VM boundary looked
substantially lower, while the exact-input pair's compute CPU medians differ
by about 0.12 seconds amid much larger within-run variation. Several compute
medians increase; scoped `Qed` increases. No native nested event durations are
summed. No end-to-end, overall-efficiency or competitive claim follows.

[The proof-complete trial patch](../../tools/eunoia-context-profile/prechecked-context.patch)
is evidence only, not a default-loaded implementation. It applies to the
`41c93f5` context-module sources; its SHA-256 is
`8900efcf949a02520a53a4f428c4fb4e31b8656ea49d08fbf3aeeaf2efd84558`.
To reproduce in an authorized disposable checkout:

```sh
git apply --check tools/eunoia-context-profile/prechecked-context.patch
git apply tools/eunoia-context-profile/prechecked-context.patch
/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2 @install \
  theories/checker/eunoia/EunoiaContextTests.vo
ROCQ_PROFILE_COMPONENTS=-unification python3 -B tools/eunoia-context-profile/run.py \
  --output /tmp/context-candidate --repeat 2 --timeout 180 --controls
ROCQ_PROFILE_COMPONENTS=-unification python3 -B tools/eunoia-context-profile/paired.py \
  --profiles /tmp/context-candidate --output /tmp/context-paired --repeat 3
```

Remove the patch with `git apply -R` and rebuild before using restored artifacts.
The retained concrete controls target is
`theories/checker/eunoia/EunoiaContextTests.vo`. The coordinator can add that
exact target to the existing eunoia `runtest` alias; no shared Dune or tactic
integration file was edited by this child.

## Validation commands and retained artifacts

All commands below ran from
`/home/charles/.t3/worktrees/SMTRocq/t3-28506d9e` through the required private
wrapper. The authorized dependency fast-forward is
`41c93f5ed49483c498900d1a25c27028142a830a`. No backend, shared Dune/tactic,
`EoRuntime.v`, solver settings or dependency installation was changed by this
experiment after the dependency fast-forward.

The initial `46c461f` baseline install and public driver exited 0, retained at
`/tmp/smtrocq-context/baseline-build.log` and `/tmp/smtrocq-context/before/`.
The matching `41c93f5` baseline and trial install builds also exited 0, with
`/usr/bin/time -v` CPU/wall rows in
`shared-runtime-build.log` and `candidate-install.log`. The exact paired
measurement commands were:

```sh
ROCQ_PROFILE_COMPONENTS=-unification /usr/bin/time -v python3 -B \
  tools/eunoia-context-profile/run.py --output /tmp/smtrocq-context/runtime-before \
  --repeat 2 --timeout 180 --controls
ROCQ_PROFILE_COMPONENTS=-unification /usr/bin/time -v python3 -B \
  tools/eunoia-context-profile/run.py --output /tmp/smtrocq-context/runtime-after \
  --repeat 2 --timeout 180 --controls
ROCQ_PROFILE_COMPONENTS=-unification /usr/bin/time -v python3 -B \
  tools/eunoia-context-profile/paired.py --profiles /tmp/smtrocq-context/runtime-after \
  --output /tmp/smtrocq-context/paired --repeat 3 --timeout 240
python3 -B tools/eunoia-context-profile/summarize.py \
  /tmp/smtrocq-context/runtime-before /tmp/smtrocq-context/runtime-after
```

All four exited 0. Raw process and per-transaction CPU/wall records are in
`/tmp/smtrocq-context/{runtime-before,runtime-after,paired}` and their adjacent
`*-driver.log` files. Exact commands, exits and elapsed time for the broader
candidate validation are in
`/tmp/smtrocq-context/validation/status.json`:

```sh
/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2 @install \
  theories/checker/eunoia/EunoiaContextTests.vo \
  unit-tests/eunoia_uf.vo unit-tests/eunoia_lia.vo
EUNOIA_KEEP_TEST_DIR=1 /home/charles/code/friends/.toolchains/smtrocq-env \
  dune runtest -j2 tools/eunoia theories/checker/eunoia \
  src/eunoia_backend src/eunoia_witness
```

Those exited 0 in 459.480 and 67.441 wall seconds respectively. All 22 UF and
15 LIA/mixed positives closed with `Qed`; the source false controls also passed.
The generated suite ran 42 Python tests and independently compiled and checked
all 29 fixtures: **994 generated derivations plus 37 explicit pushes** (1031
trace computation commands). Retained generator artifacts are at
`/tmp/smtrocq-eunoia.UvfCCxlV/`. Existing semantic gates, nested scope tests,
backend replay/corruption controls, and all 75 witness cases passed.

The initial 49-target audit exited 0 (29.086 seconds), including all 13 new
trial refinement lemmas and all 13 new concrete tests. Its public-name selection
matched only unindented declarations, so it included only two UF exports.
A separate explicit audit corrected that enumeration to cover **every** public
UF/LIA declaration and the three scoped `*_with_correct` wrappers: 43 targets,
exit 0, 39.673 seconds, no new assumptions. Sources and exact commands are in
`/tmp/smtrocq-context/validation/assumptions/summary.json` and
`/tmp/smtrocq-context/public-audit-command.json`; the corrected public reports
are `/tmp/smtrocq-context/public-assumptions/summary.json`.
All 30 paired proof audits passed in `paired/CASE/audit/summary.json`.
The separately recorded 13-lemma refinement audit also passed.

The main recursive `rocq check -silent -bytecode-compiler yes` invocation
imported both complete public suites, the concrete controls, generic machines
and tactic modules: exit 0, **236.139 seconds**, with all hashed proof artifacts
unchanged. The exact command/loadpaths and hashes are in the validation status
JSON. The separate combined recursive check of all five paired modules also
exited 0 (86.315 seconds); exact arguments are in
`/tmp/smtrocq-context/paired/kernel/command.json`. Neither command admits or
skips dependencies. Candidate installed proofs and both public suite artifacts
were copied to `/tmp/smtrocq-context/candidate-artifacts/` before restoration,
so the evidence does not rely on later restored `.vo` files.

The existing profile harness unit tests also passed (6 tests, exit 0), logged in
`/tmp/smtrocq-context/profile-unit.log`.

After rejecting the trial, all eight profiled production-module source hashes
were checked against the matching pre-trial snapshot and matched exactly.
The final restored build, concrete eunoia/backend/witness tests, 19-target audit
(13 controls plus six public correctness wrappers), and recursive kernel check
of the new controls all exited **0**. The exact commands, exit codes, elapsed
times and restoration assertion are in
`/tmp/smtrocq-context/restored/status.json`; the final assumption comparison is
`/tmp/smtrocq-context/restored/assumptions/summary.json`, with no added assumptions.
This final pass does not repeat the complete 37-goal public suite: that suite
was rebuilt, audited and kernel-checked with the trial; the restored production
sources are byte-for-byte the authorized parent baseline. Generated runtime
sources were unchanged throughout this final restoration. `git apply --check`
on the retained trial patch also exited 0 after restoration.

## Handoff and remaining work

Final branch: `t3/eunoia-context-performance` (initial profiler metadata records
`t3/28506d9e`), based on authorized parent `41c93f5`. Evidence commit:
`2d194567f1ca3472e3c3bd8558557c3460c122e2`. Local commits contain
only the new concrete tests, profiling/reproduction tools, proof patch and
measurement/report evidence. No production context optimization is integrated.
No push, PR, GitHub comment, subdelegation, system install, shell configuration
change, new assumption or proof hole was used.

The coordinator owns default alias registration of `EunoiaContextTests.vo`.
A larger controlled benchmark and improvements to the still-expensive generated
checker conversion remain open. The whole repository build/test matrix was not
rerun by this child; the focused generated, concrete, witness, backend and
complete public UF/LIA validation above is the scope of this result. Overall
port completion and overall/competitive efficiency remain unestablished.

The retained patch normalizes blank context-line markers to avoid whitespace
checker false positives. It applies successfully and reproduces all six measured
candidate source hashes exactly (`/tmp/smtrocq-context/patch-format-check/`).
The coordinator's later `604c043` runtime/witness diagnostic was received after
this frozen experiment; its development timings were not mixed into this pair.
No full benchmark matrix was started.
