# Witness scheduling and certificate allocation

This is an isolated development performance investigation, not backend
acceptance or a final benchmark matrix. Worktree:
`/home/charles/.t3/worktrees/SMTRocq/t3-0bcf48f5`, branch
`t3/optimize-witness-search`. The starting parent was `f965e57`; dependency
merge `1f9f840` incorporates the authorized `c79eeba` handoff (live LIA,
generated integer tightening, and public LIA registration). No helper-marshaling,
backend, generator, checker, shared Dune or tactic changes are authored here.

## Diagnosis

`EUNOIA_WITNESS_PROFILE=1` prints the exact ordered implications and optional
stage samples to stderr. `cpu_s` is cumulative **process CPU time within that
producer call**, not wall time, solver time, gate time, or whole tactic time.
Begin/end/raise events identify interrupted stages. The development runner
records compiler wall time separately, with source hashes, plugin hashes,
commands, exits, timeout flags and system load averages. Profiling is disabled
by default and is never an acceptance test.

The original hypothesis was that unrestricted propositional saturation blocked
the first arithmetic attempt for the two slow original benchmarks. It does run
first, and makes unnecessary local clauses, but the measured native producer
does **not** account for their whole-compiler timeouts. On the merged parent,
all 140 disjunctive and 124 inconsistent local producer calls finish before
the compiler's 30-second timeout. No search stage is left open. Whole-compiler
work after search belongs to the remaining production validation/proof path;
these measurements alone do not isolate which part of that path is slow.

Matched original statements, 30-second compiler boundary, same private
toolchain, shared default fuel, solver and configured search limits:

| Disjunctive bounds diagnostic | Before scheduling | After scheduling only |
| --- | ---: | ---: |
| Producer calls | 140 | 140 |
| Sum of last stage CPU readings (seconds) | 0.056828 | 0.012556 |
| Sum of searched slot counts | 4173 | 2308 |
| Resolution pairs | 9646 | 2558 |
| Largest local search slot count | 696 | 161 |
| Whole compiler | 30-second timeout | 30-second timeout |

These are sequential development probes alongside other jobs, not calibrated
latency estimates. System load averages are retained in each command record.
The largest implication is a Boolean congruence between two implications with
nested conjunctions and disjunctions. It uses 3377 pairs before and 356 after
scheduling. Its local resolution stage decreases from roughly 0.027 CPU
seconds to under 0.001. Formula and source-step counts are unchanged.

For inconsistent bounds, the corresponding 124 calls use 3409 searched slots
and 7302 pairs before scheduling, versus 2076 slots and 2234 pairs after it;
the peak local search drops from 383 to 124 slots. The compiler times out
after search in both runs. The completed stage CPU readings sum to 0.027088
and 0.018068 seconds respectively.

With final compaction, disjunctive bounds retains 1322 slots across its 140
candidates (1033 commands plus every root). Inconsistent bounds retains 1121
slots across 124 candidates (860 commands plus every root). Both have a peak
candidate capacity of 35. Search still discovers the same 2308/2076 slots as
the scheduling-only version; no search budget was relaxed. The largest
disjunctive candidate searches 161 slots but emits only 35 (three roots and
32 commands). Its original unpruned allocation was 696 slots. Compaction
reduces gate allocation, but both original large goals still time out at
30 seconds in the final diagnostic.

Evidence is under `/tmp/smtrocq-witness-performance/`:

* `parent-before/`: matched parent plus profiling, original scheduling;
* `index-after/`: registration indexing and arithmetic scheduling;
* `compact-after/`: final scheduling and dense certificate allocation;
* `uf-shaped-after/`: six original UF benchmark statements over `Z`, copied
  from `benchmarks/eunoia/cases.json` into retained standalone public proofs;
* each directory's `results.json`, `metadata.json`, copied sources,
  `command.json`, `output.log` and `*-summary.json`;
* `before/` is an earlier f965 diagnostic, overlapping the initial build.
  Its plugin predates exact-input printing; it is not the matched comparison.

In the final 30-second development diagnostic, all six original LIA
statements time out (exit `-9`, explicitly killed by the runner), including
strict shift. It proceeds through local witness generation rather than an
immediate missing-rule report, but that is not a checked live proof claim.
The UF-shaped integer congruence, binary congruence and predicate congruence
proofs compile with exit 0 in 9.059, 19.818 and 24.250 seconds respectively;
transitive congruence, nested congruence and equality chain time out. These
probes overlap the separate correctness compilation and other jobs. Load
averages rise from roughly 5 to 23 across the development session, so this
does not isolate latency improvements or establish intrinsic 30-second
coverage. It does preserve the requested compiler boundary and expose the
remaining after-search cost. No comparison with another solver was run.

## Changes and trust boundary

Previously clauses were indexed only after removal from the nonunit queue.
Consequently `resolve_pending ~units_only:true` could not propagate through
unselected Boolean definitions or premise clauses. Indexing at registration
lets the unit queue reach those clauses immediately. Pair memoization still
checks each ordered binary-resolution candidate once, and self-pairs are
ignored. Unrestricted saturation remains available when needed.

After adding EUF candidates, search propagates units, attempts the exact
arithmetic implication and arithmetic-unit conflict, then runs unrestricted
resolution. This is generic scheduling with no CPC rule-name input. Whole
disjunctive premises remain auxiliary disjunctions, never assumed disjuncts.

Search already slices its local command DAG at conflict. The new finishing
pass also compacts retained command slots. Every ordered root claim, including
unused and duplicate roots, keeps its original slot and clause. Retained
commands have fresh consecutive destinations, with explicit reads and the
conflict slot relocated consistently. Formula/literal indices, exact expected
clauses and Micromega evidence do not change. Candidate capacity is precisely
the number of roots plus retained commands; the **search** clause budget is
still enforced on every discovered slot before pruning/compaction.

Every resulting command remains untrusted and is recomputed by the existing
local semantic gate. No authoritative root or original generated CPC step is
removed. The backend still checks unused source steps. No solver result,
producer success or performance trace is accepted as a proof. No configured
clause, pair, term, formula, theory-round, arithmetic, fuel, solver or compiler
limit is increased. No Rocq soundness lemma or assumption is introduced.

## Reproduction

Use only `/home/charles/code/friends/.toolchains/smtrocq-env` and the existing
private cvc5 1.4.2 (`282d5e0`). No installation or network access is needed;
neither Logos nor Ethos was used.

```sh
E=/home/charles/code/friends/.toolchains/smtrocq-env
"$E" dune build -j2 src/eunoia_backend/eunoia_backend.cmxs \
  src/eunoia_witness/eunoia_witness.cmxs theories/SMTCoq.vo
python3 tools/eunoia-witness-profile/run.py --profile \
  --output /tmp/witness-profile-example --timeout 30 \
  /tmp/smtrocq-lia-milestone-benchmark/runs/cvc5_eunoia/lia_disjunctive_bounds/1/case.v \
  /tmp/smtrocq-lia-milestone-benchmark/runs/cvc5_eunoia/lia_inconsistent_bounds/1/case.v
python3 tools/eunoia-witness-profile/summarize.py \
  /tmp/witness-profile-example/0-lia_disjunctive_bounds-case/output.log
"$E" dune runtest -j2 src/eunoia_witness/tests src/eunoia_backend/tests
bash src/eunoia_witness/tests/verify-local-gate.sh \
  "$PWD/theories/checker/eunoia/EunoiaLocal.v"
```

The runner records timeout outcomes and intentionally exits normally after
recording them: inspect each row's `exit_code` and `timeout`, not the driver's
exit alone. Never replace a valid expected goal by `Fail` to obtain a pass.

## Integration and remaining work

The two original large statements remain positive cases in the existing
benchmark suite; neither is removed or changed into an expected failure.
An optional two-goal public source with `Qed`, `Print Assumptions` and a false
disjunctive-bound control is retained only as a development artifact at
`/tmp/smtrocq-witness-performance/frozen/eunoia_lia_bench.v`. Its first proof
did not close after 460.742 wall seconds and the compiler was explicitly
terminated (compiler exit `-15`, draft driver exit `241`). No new public test file is committed or proposed for
registration without a successful compile, audit and kernel check. This
abandoned uncapped diagnostic is not a passed proof or a latency measurement.
No shared Dune changes are required. Existing 15 LIA and 22 UF public
goals and all 75 original native/gate cases remain intact; two nested Boolean
implication cases extend the local suite to 77. Dense allocation and fresh
reads are checked throughout the native/gate suite. Gate mutation controls
continue to alter capacity, roots, conclusions, expected clauses and theory
evidence, exercising the actual checked boundary.

## Local verification

Code commit `672cc46b655058d5bbce33ab2d08f417d6ee80dd` passed:

* `smtrocq-env dune runtest -j2 src/eunoia_witness/tests src/eunoia_backend/tests`:
  exit 0, including the unchanged backend source/evidence mutation tests;
  `/tmp/smtrocq-witness-performance/compact-native.log`.
* `smtrocq-env dune build -j2 src/eunoia_witness/eunoia_witness.cmxs`: exit 0,
  `/tmp/smtrocq-witness-performance/compact-build.log`.
* `bash src/eunoia_witness/tests/verify-local-gate.sh
  "$PWD/theories/checker/eunoia/EunoiaLocal.v"`: exit 0, all 77 native/gate
  cases with mutation rejection. Complete typed VM replay and gate assumption
  output: `/tmp/smtrocq-witness-probe.39n14i/`. The copied gate hashes to
  `feb60ebc93dc614ab348fbb3d3c9ccf461b38f958ee6be3751a101b9cb094dcd`.
* Ordinary public `rocq c` on the exact existing 22-positive UF file and
  15-positive LIA file: both exit 0, including their false controls and
  `Print Assumptions` commands. These uncapped correctness compiles take
  271.490 and 563.993 wall seconds under concurrent load. Their commands and
  exits are in `/tmp/smtrocq-witness-performance/frozen-status.json`.
* Complete baseline assumption audit of **all 40 exported declarations** in
  those files (22 UF positives, 15 LIA positives and three false-control
  examples): exit 0, no additional assumptions. Exact arguments and results:
  `/tmp/smtrocq-witness-performance/core-verification.json` and
  `core-assumptions/summary.json`. The scan includes declarations indented
  inside the UF Section. A first draft driver missed those names; this full
  audit supersedes that incomplete selection.
* Independent recursive `rocq check -silent` on both complete public modules,
  without admission flags: exit 0, same command record and
  `/tmp/smtrocq-witness-performance/core-kernel.log`.

The standalone sources are copied under
`/tmp/smtrocq-witness-performance/frozen/` with logical prefix `WitnessPerf`.
Their bytes match the repository sources. The complete imported `.vo` and
`.cmxs` fingerprint is in `frozen-artifacts.json`; `core-changed-artifacts.json`
is `[]` after these checks. No build is run during this proof verification.
The audit inherits only dependencies admitted by the existing baseline,
including the existing Uint63 specifications and proof irrelevance as reported;
it is not described as assumption-free. No new soundness lemma needs a
separate `Print Assumptions` command.

The existing public smoke file also passes ordinary compilation, baseline
assumption comparison for all five exported declarations, and independent
recursive kernel checking (all exits 0). Exact commands/results are in
`/tmp/smtrocq-witness-performance/smoke-status.json`; the unchanged source
includes three live positive proofs (including the quantified-carrier
regression) and two false controls.

The optional large-goal run is incomplete, as described above. Its exact
command, cancellation exit and elapsed time are retained as the third row in
`frozen-status.json`; that file is **not** an all-passing acceptance summary.
The successful required-suite verification is `core-verification.json`, plus
`smoke-status.json`. The unused draft/full-suite audit drivers under the
scratch directory are not verification evidence for that optional file.
`/tmp/smtrocq-witness-performance/final-summary.json` consolidates all nine
required successful stages and records the optional cancellation separately;
`changed-artifacts.json` is still `[]` at final handoff.

All required live files, the native/gate cases and backend replays pass, but
the requested whole-compiler 30-second goal remains unmet for all six LIA
cases and three UF-shaped integer cases. Remaining expensive work after
native witness production requires the coordinator's separate helper/runtime
work and a fresh composed regression. No overall backend completion or final
benchmark acceptance is claimed here.
