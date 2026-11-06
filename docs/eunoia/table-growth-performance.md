# Authoritative table growth investigation

This child investigation starts at `8a739b72d5fe994690035bc33740e5fe5ab74524`
on `t3/eunoia-table-growth`. It is independent of backend checked-certificate
reuse. The coordinator owns integration. No overall completion or competitive
performance result is claimed.

## Measurement contract

`EUNOIA_TABLE_PROFILE=1` enables an observational wrapper around native witness
production. It snapshots authoritative atom/form counts immediately before and
after each call and reports recursive source and retained-certificate dependency
indices. It never removes table entries, changes indices, mutates inputs or
accepts a witness. With the option absent, the existing producer is called
directly. `EUNOIA_WITNESS_PROFILE=1` independently exposes existing native stage
CPU samples; those are not checker/compiler timings.

Counts exclude the array sentinel: `Atom.to_array` has `count + 1` cells and
`Form.nvars` is the declared form count (including true/false). The initial
prefix and all inter-call growth are conservatively source-required. The union
of all later source dependencies is applied before labeling search-created
entries unused; a source result can reuse an earlier search entry without
increasing either count. Retained dependencies include every ordered root,
action literal and expected-clause literal, their recursive formula children,
and recursive atom children. A certificate-only dependency is one not also
source-required. Arithmetic proof variable numbering follows the original
clause's atom traversal and cannot be changed by renumbering table entries.

`tables-summary.json` classifies entries at the **last completed witness
boundary**. Open calls are explicit. A timeout after all search calls is still
a failed compiler probe and supplies no checked theorem. The first boundary
includes initial authoritative roots even if they never appear in a local
implication. Later original source results, including unused steps, remain
represented in the source union.

The backend reifies ordinary results immediately before invoking witness
production. Thus the preceding search-end and next search-begin counts give
the exact before/after counts for that result in an ordinary trace. In scoped
traces, a push can intervene: those boundaries report the exact **combined**
push/result growth, not separate timings or counts for each. The witness API
has no pre-reification callback. Separately observing the first result before
reification and individual pushes requires coordinator-owned backend hooks
around `reify t st.result` and `reify t assumption`; this child does not edit
backend files. No table changes occur in certificate marshaling.

## API constraints

Inspection of `src/common/smtAtom.ml` and `smtForm.ml` establishes:

* `get ~declare:false` constructs a value with index `-1`, without lookup or
  insertion. It does not reserve a stable index or roll back a previous get.
* Atom exposes a copy operation, but Form exposes neither copy nor rollback.
* The backend snapshots final authoritative tables after **all** witness calls.
  Local command DAG slicing therefore does not remove discarded global entries.

No speculative rollback, table reconstruction, source-root shrinking or
Micromega renumbering is justified by those APIs. All original CPC derivations
and every emitted local certificate must still pass the existing generated
computation, exact bindings and semantic gate.

## Reproduction

All dependencies remain under `/home/charles/code/friends/.toolchains`.
No install, network, Logos or Ethos reference was needed.

```sh
/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2 @install
python3 -B tools/eunoia-table-growth-profile/run.py \
  --output /tmp/table-growth-example --timeout 30 \
  /tmp/smtrocq-composed-runtime-witness-diagnostic/benchmark/runs/cvc5_eunoia/uf_congruence/1/case.v
python3 -B tools/eunoia-table-growth-profile/summarize.py \
  /tmp/table-growth-example/0-0-uf_congruence-case/output.log
python3 -B tools/eunoia-table-growth-profile/test_summary.py
```

The runner copies theorem files verbatim, preserves `Time cvc5_eunoia`,
`Time Qed` and `Print Assumptions`, uses fresh compiler processes, and records
commands, exits, source/plugin/proof hashes, CPU/wall times, load averages and
whether a fresh `.vo` and the source's checked marker exist. It does not audit
assumption output or establish kernel acceptance itself. A driver exit 0
means its records were written consistently, not that all positives passed.
Run only one public tactic per compiler when aggregating table indices;
the summary rejects observable table resets. Resource limits, default fuel,
solver flags and the 30-second compiler boundary are unchanged.

The focused measurements and integration limits follow below.

## Narrow candidate

The trial changes only `lia_candidate`'s helper constructors to
`Form.get ~declare:false`. It keeps original atom objects, formula polarity,
Boolean expansion structure, clause canonicalization before evidence production,
and atom traversal order. Inspection of `src/lia/lia.ml` shows that its native
formula traversal uses only `Form.pform`, `Form.is_pos`, and original atoms.
Its variable map is keyed by those atoms; transient helper form indices are
never looked up or emitted. `LiaMicromega` still carries the original clause,
which the existing Rocq gate rebuilds and checks. Each future source formula is
reified normally, regardless of whether a similar helper was tried earlier.
There is no rollback or renumbering of existing entries.

The trial adds native/real-gate XOR and ITE arithmetic cases to the original 77
cases. Assertions on those and the existing IFF integer-gap case require that
these helper expansions do not increase the authoritative formula count.
These are positive cases with actual checked evidence, including mutation
controls in the gate probe; they are not expected-failure substitutions.

## Focused development measurements

Raw evidence: `/tmp/smtrocq-table-growth/{before,after}/`, including each
`metadata.json`, `results.json`, `command.json`, `output.log` and
`tables-summary.json`. `comparison.json` consolidates the exact records.
The initial build, native trial and profiling driver commands exited 0.
All trial/baseline source-result calls finished before the compiler boundary;
none of these timeouts was an unfinished native witness call.

| Case | Calls | Atoms (both) | Forms baseline / trial | Unused forms baseline / trial |
| --- | ---: | ---: | ---: | ---: |
| uf_congruence | 13 | 13 | 28 / 21 | 11 / 4 |
| uf_transitive_congruence | 27 | 40 | 75 / 49 | 39 / 13 |
| uf_nested_congruence | 25 | 46 | 79 / 53 | 44 / 18 |
| lia_disjunctive_bounds | 140 | 176 | 317 / 210 | 150 / 43 |
| lia_inconsistent_bounds | 124 | 98 | 253 / 166 | 113 / 26 |
| lia_integer_gap | 28 | 30 | 77 / 38 | 40 / 1 |

| Case | Baseline wall / CPU seconds | Trial wall / CPU seconds | Compiler exits baseline / trial |
| --- | ---: | ---: | ---: |
| uf_congruence | 5.075 / 5.097 | 6.235 / 6.164 | 0 / 0 |
| uf_transitive_congruence | 30.037 / 30.203 | 30.008 / 30.178 | -9 / -9 |
| uf_nested_congruence | 30.027 / 30.196 | 30.049 / 30.219 | -9 / -9 |
| lia_disjunctive_bounds | 30.011 / 30.186 | 30.008 / 30.172 | -9 / -9 |
| lia_inconsistent_bounds | 30.010 / 30.172 | 30.008 / 30.167 | -9 / -9 |
| lia_integer_gap | 29.545 / 29.681 | 30.009 / 30.179 | 0 / -9 |

CPU is compiler-process-tree user plus system time, recorded via
`getrusage(RUSAGE_CHILDREN)` deltas, including waited solver children. Each
compiler has the same original 30-second whole-process wall boundary.
Exit `-9` is the runner killing a timeout; it is never a positive result.
Fresh proof artifacts and checked markers exist only for exit-0 probes.

Both tracing options were enabled in both runs, so these compiler timings
include observational profiling overhead. These are single sequential probes
under concurrent load: 24 reported CPUs,
1-minute load averages 4.530–6.232. They establish table-size
reduction but **no measured whole-compiler benefit**. In particular integer-gap
finished before the boundary in the baseline but timed out in the trial.
The small UF control was also slower in the trial. They do not establish a
calibrated slowdown estimate, nor a new intrinsic coverage limit.

Only `rocq-smtcoq/eunoia_witness/eunoia_witness.cmxs` changed between
the two imported artifact manifests; all 51 `.vo` files and other plugins
were identical. Artifacts and measured search sources stayed unchanged
within each run (`artifacts_unchanged` and `search_unchanged` are true).
All theorem-source SHA-256 values match pairwise. See
`artifact-comparison.json`. The cvc5 solver cleans its temporary CPC files;
this investigation does not claim to have archived or hashed those deleted
solver outputs. Its binary, signature, flags, source goals and fuel were fixed.

## Decision

The transient-helper optimization is **rejected**. Production search uses
the original interning behavior. The producer body is byte-for-byte the
starting implementation except for its private function name;
`/tmp/smtrocq-table-growth/restoration.json` records the comparison.
Only opt-in tracing and two additional arithmetic regression cases remain.
The small trial and its stronger no-growth test assertions are retained as
`tools/eunoia-table-growth-profile/transient-lia-helpers.patch`, which passes
`git apply --check` against the final files. It is an experiment, not integrated
production code. The trial itself passed all 79 native/real-gate cases and
mutation checks (`candidate-native.log`, `candidate-gate.log`, gate scratch
`/tmp/smtrocq-witness-probe.hbKxCv/`), but was not given a full public-suite
acceptance run.


The same observations are plotted in
[`observations.html`](../../tools/eunoia-table-growth-profile/observations.html).

The exact six-source invocations were:

```sh
B=/tmp/smtrocq-composed-runtime-witness-diagnostic/benchmark/runs/cvc5_eunoia
python3 -B tools/eunoia-table-growth-profile/run.py \
  --output /tmp/smtrocq-table-growth/before --timeout 30 \
  "$B/uf_congruence/1/case.v" "$B/uf_transitive_congruence/1/case.v" \
  "$B/uf_nested_congruence/1/case.v" "$B/lia_disjunctive_bounds/1/case.v" \
  "$B/lia_inconsistent_bounds/1/case.v" "$B/lia_integer_gap/1/case.v"
# Apply only the retained experiment patch when reproducing the trial.
# Do not leave the trial applied for integration.
/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2 \
  src/eunoia_witness/eunoia_witness.cmxs src/smtcoq.cmxs \
  src/eunoia_witness/tests/search_tests.exe
python3 -B tools/eunoia-table-growth-profile/run.py \
  --output /tmp/smtrocq-table-growth/after --timeout 30 \
  "$B/uf_congruence/1/case.v" "$B/uf_transitive_congruence/1/case.v" \
  "$B/uf_nested_congruence/1/case.v" "$B/lia_disjunctive_bounds/1/case.v" \
  "$B/lia_inconsistent_bounds/1/case.v" "$B/lia_integer_gap/1/case.v"
```

Both profiling drivers exited 0 while recording the individual failed probes
above. `/tmp/smtrocq-table-growth/{before,after}-driver.log` retains their output.
The trial's direct native execution was:

```sh
/home/charles/code/friends/.toolchains/smtrocq-env dune exec \
  src/eunoia_witness/tests/search_tests.exe
bash src/eunoia_witness/tests/verify-local-gate.sh \
  "$PWD/theories/checker/eunoia/EunoiaLocal.v"
```

Both exited 0 with 79 cases; the second runs actual typed VM gate computation
and its existing capacity/root/conclusion/clause/theory-evidence mutation
controls. The unchanged original producer has been restored before final
validation. No compiler limit was changed to turn a timeout into success.

## Parent update during validation

The coordinator reported parent `4f87e02` while this child's frozen public
correctness compile was running. That parent adds synchronous Abstract
checked-certificate caching, rollback controls and a final exact check;
the coordinator states that Search/runtime/gate inputs match `8a739b7`.
This child does not rebase or edit the parent's files. The measurements above
remain against the `8a739b7` backend, and **do not measure composition with
certificate reuse**. The retained experiment patch can be reconsidered in a
separate exact-input pair after the coordinator integrates the tracing tools.
The frozen parent acceptance run belongs to the coordinator, not this report.

## Final restored verification and handoff

Final source branch: `t3/eunoia-table-growth`, based on `8a739b7`. Code commits:

* `5e02f08a3c5b9c1537b5c9d15590bb69b41776a8`: opt-in tracing and profiling tools.
* `5a6e7f4361531acb7416314123cd11b6ef3b2a82`: include FbbT formula children in dependency tracing.
* `c90db19cf940f45576e7e8b212799a4c45a3c9ef`: arithmetic XOR/ITE native and gate regressions.

All final verification stages below exited **0**. Commands, individual arguments,
CPU/wall/load rows and paths are retained in
`/tmp/smtrocq-table-growth/validation/status.json`. The executed driver source is
`/tmp/smtrocq-table-growth/validate.py` (invoked as `python3 -B` from this
worktree); `validation-driver.log` contains its command records.

| Stage | Wall seconds | CPU seconds | Result |
| --- | ---: | ---: | --- |
| native-backend | 79.603 | 103.860 | 79 native cases plus unchanged backend replays/corruption controls |
| gate | 8.382 | 8.569 | 79 native/real-gate cases and mutations |
| public-build | 476.049 | 684.276 | 22 UF + 15 LIA/mixed + 3 smoke positives Qed; false controls pass |
| assumptions | 48.767 | 49.467 | 56 main/public targets, no new assumptions |
| recursive-kernel | 100.707 | 102.448 | Independent recursive kernel check, no admission flags |

The public build is an uncapped **correctness** run of the existing suites,
not an additional successful 30-second benchmark. Every positive retains its
original statement and `Qed`. The passing source suites cover supplied and
duplicate roots, multiple sorts, the exact fully quantified carrier universe,
negative predicates and scoped exports. No public suite, theory, common
semantics, runtime, backend, generator, tactic or Dune source was edited here.

The complete audit explicitly enumerates all 45 public/smoke exports, including
indented UF Section declarations, and the original 11 main/default-fuel targets.
Its summary is `validation/assumptions/summary.json`. Three additional scoped
`*_with_correct` targets passed separately (exit 0, 3.843 seconds):
`scoped-audit-command.json` and `scoped-assumptions/summary.json`. All **59**
targets remain within the existing 52-name assumption baseline. This means no
new assumptions, not assumption-free proofs. No new Rocq soundness lemma was
added, so there is no new lemma requiring a separate assumptions command.

The exact recursive kernel command was:

```sh
/home/charles/code/friends/.toolchains/smtrocq-env rocq check -silent -Q /home/charles/.t3/worktrees/SMTRocq/t3-9f6cf63a/_build/install/default/lib/coq/user-contrib/SMTCoq SMTCoq -Q /home/charles/.t3/worktrees/SMTRocq/t3-9f6cf63a/_build/default/unit-tests SMTCoq.tests SMTCoq.checker.eunoia.EunoiaChecker SMTCoq.checker.eunoia.EunoiaScope SMTCoq.checker.eunoia.EunoiaLocal SMTCoq.checker.eunoia.EunoiaAdapter SMTCoq.tests.eunoia_uf SMTCoq.tests.eunoia_lia SMTCoq.tests.eunoia_tactics SMTCoq.eunoia_backend_tests.Proof SMTCoq.eunoia_backend_tests.Public SMTCoq.eunoia_backend_tests.Lia SMTCoq.checker.eunoia.EunoiaTactic SMTCoq.checker.eunoia.EunoiaScopedAdapter
```

The complete imported plugin/proof fingerprint is
`validation/artifacts-before.json`; `validation/changed-artifacts.json` is
`[]` after the audit and recursive check. No build runs during that final
artifact verification. The final actual gate replay and its printed gate
assumptions are retained in `/tmp/smtrocq-witness-probe.EOFJnY/`.
The four profiler-accounting tests pass (exit 0, `profile-tests.log`). Direct
native execution with `EUNOIA_TABLE_PROFILE=1` also exits 0 and has the same
78 printed PASS rows as the disabled run (79 registered cases, including the
separate noncanonical-input case); see `profile-enabled-native.log`.
`git diff --check` and `git apply --check` on the retained trial patch pass.

Remaining work: no whole-compiler improvement is established, the large timed
positives still time out, and the trial is not integrated. Counts before the
first source-result reification and separate push/result counts in scopes need
the narrow coordinator-owned backend hooks described above. Composition with
`4f87e02` and any final benchmark matrix belong to coordinator integration.
No default alias or shared-file change is required for the retained cases;
the existing witness library/test stanzas pick them up. No push, PR, GitHub
comment, delegation, system install, proof hole or new semantic assumption was
used. Overall port completion remains outside this child's result.
