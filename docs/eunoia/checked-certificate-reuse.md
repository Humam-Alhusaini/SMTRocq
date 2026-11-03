# Same-invocation checked certificate reuse

This is a focused backend investigation from parent `604c043`, not completion
of the cvc5/Eunoia port or a final benchmark. Changes are confined to backend
proof construction and independent developer probes. The generated checker,
semantic gates, witness producer, resource limits and checker interfaces are
unchanged.

## Trust and API boundary

The original tactic calls `EunoiaRocq.checked_true` (a full VM conversion),
embeds the resulting VM cast in a correctness application, and runs
`Tactics.exact_check`. `Qed` checks the embedded cast again. Supplied-lemma
proofs additionally typecheck an intermediate refutation. The public
`build_refutation[_from_cpc]` contract requires that intermediate check and
returns its constraints through the caller's actual sigma reference.

The experiment uses Rocq's supported
`Abstract.cache_term_by_tactic_then ~opaque:true` API, rather than declaring
constants or changing global proof state itself. Its helper's proposition is
the equality of the **complete, applied checker** with `true`. All tables,
models, names, fuel, goal/root bindings, source payloads, nested trace,
conflict, and local evidence remain in that exact application. Nothing is
looked up in a semantic cache or reused across contexts.

On the installed Rocq 9.3.0 / OCaml 4.14.2 implementation, the relevant source
path is:

1. `tactics/abstract.ml:cache_term_by_tactic_then` generalizes the actual
   proof-local context, handles fresh names and Section variables, and calls
   `Subproof.declare_abstract`.
2. `proofs/subproof.ml:declare_abstract` runs the supplied proof tactic to
   completion and builds an `OpaqueEff` containing its body and exact type.
3. `engine/evd.ml:push_side_effects` calls
   `Safe_typing.add_private_constant`.
4. `kernel/safe_typing.ml:add_private_constant` calls `infer_direct_opaque`,
   which immediately invokes `Constant_typing.check_delayed` on the body.
   A private certificate stores the checked body for subsequent saving. The
   abstraction callback runs only after this synchronous kernel check.

These installed sources are under
`/home/charles/code/friends/.toolchains/opam/smtrocq/lib/rocq-runtime/`.
The ambient private constant can have a type-only representation inside the
proof environment; its body is retained in the checked side effect. When
Rocq saves the main opaque theorem, `Safe_typing.check_opaque` and
`inline_side_effects` put monomorphic helper bodies into lambda applications
and substitute polymorphic bodies. The saved proof thus contains the helper
body, rather than depending on an exported helper name. Rocq's standard
private-proof certificate avoids checking an already checked body again
during that save. Independent recursive kernel checking checks the saved
body, including its VM cast. No flags or certificate mechanisms are changed
by the backend. No delayed global declaration API is used.

Both checking the helper and creating/exporting it must remain inside the
measured tactic. The final correctness application must still pass
`Tactics.exact_check` and `Qed`. The public builder functions must continue
to check the returned complete refutation and preserve the actual sigma.
Invalid certificates must fail inside the tactic, before any successful
private-helper reuse.

## Reproduction tooling

Build through the existing private environment wrapper. No installation or
shared Dune stanza is necessary:

```sh
/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2 @install \
  src/eunoia_backend/eunoia_backend.cmxs \
  src/eunoia_backend/tests/integration/backend_test_plugin.cmxs
python3 -B tools/eunoia-proof-reuse/run.py \
  --output /tmp/eunoia-proof-reuse-run --helpers --controls
python3 -B tools/eunoia-proof-reuse/verify.py \
  --profile-dir /tmp/eunoia-proof-reuse-run \
  --output /tmp/eunoia-proof-reuse-validation
```

Omit `--helpers` on the original backend, where those declarations do not
exist. Each case uses a fresh compiler, default fuel 10000, the same source
theorem and production witness producer. The arithmetic and scoped source
replays are explicitly labeled. `Time tactic` includes all private helper
work; `Time Qed` is recorded separately. Process user/system/wall times,
native profiles, exact commands/exits, source hashes, backend plugin hashes,
and all dependency `.vo` hashes are retained. Audits check the main theorem
and, with `--helpers`, the actual saved helper bodies against the exact
existing 52-name baseline. The test-only `Eunoia_helper_assumptions` query
reads the saved opaque theorem, finds every certificate VM cast, and runs
Rocq's own `Assumptions.assumptions` walker and assumption printer on its
global dependencies. It requires at least one certificate, and never uses
introspected terms to construct a proof. This handles both monomorphic and
polymorphic inlining. Main exports still use ordinary `Print Assumptions`.
`verify.py` aggregates the checked source theorems under unique names, reruns
the tactics, audits main and helper dependencies, and recursively checks the
whole module once. Its validation compilation retains `Time` but removes
profiling. Recursive `rocq check -bytecode-compiler yes` uses no dependency
admission flags; unchanged dependency hashes are required at the end.

`Controls.v` exercises corrupted source/results/premises/roots, bad used and
unused local witnesses, scope bindings, missing intermediate instances,
false goals, Undo, Section discharge and universe polymorphism. A failed
attempt must leave no helper visible under the proof's expected fresh name.
`--controls` compiles it through the same loadpaths, audits its exports and
saved helper bodies, and with `--kernel-check` recursively checks its `.vo`.
The test plugin also checks that failed/undone attempts leave no private
proof effects in the actual sigma, rather than relying solely on names being
absent from the global name table.

Optional `table_sizes.py install --backup /tmp/eunoia-table-probe` inserts
temporary native Profile events around each witness call and records the
complete applied checker expression using `Constr.debug_print`. Atom/form slot
counts include their default slot. Restore using the same backup, then
rebuild the backend `.cmxs`; both operations verify source hashes. Counting
allocates temporary arrays, so instrumented timing is not a production
performance result. It neither edits the producer nor changes any table or
checker result.

## Focused results

The production change uses the checked helper for the tactic's Boolean,
equality and supplied-root refutation paths. The supplied-root path assembles
its complete proof before the final `exact_check`; it no longer calls the
public builder's additional intermediate typecheck. Both public builder APIs
retain their original `checked_true`, complete `Typing.type_of`, actual sigma
reference, and returned constraints. The helper and final proof use Proofview's
current sigma; no map is reset and no CompDec evars are introduced.

`src/common/smtCommands.ml:build_body` and `build_body_eq` establish the precedent
for binding shared tables/certificates in proof terms. This change uses a
stronger sharing boundary for the computation's **checked proof**. Generic
table lets alone would still leave the VM-cast computation in the saved proof
and would not eliminate its repeated checking. No speculative let machinery
or semantic cache is added alongside the measured change.

Two fresh compiler runs per case were measured at parent `604c043`, with the
same default fuel, solver, witness producer, generated source and semantic
checker. All helper creation/checking is within `Time tactic`; the table below
adds that time and `Time Qed`. CPU is user plus system time. Units are seconds;
medians of two observations are descriptive, not a statistical speed claim.

| Case | Before CPU | After CPU | Before wall | After wall |
| --- | ---: | ---: | ---: | ---: |
| Quantified abstract congruence | 4.242 | 3.820 | 4.220 | 3.842 |
| Positive predicate | 2.018 | 1.769 | 2.010 | 1.765 |
| Negative predicate | 2.533 | 1.903 | 2.572 | 2.018 |
| Two sorts, intermediate CompDec | 6.801 | 3.794 | 6.896 | 3.761 |
| Repeated supplied hypotheses | 7.671 | 4.146 | 7.620 | 4.253 |
| Live integer bound conflict | 1.947 | 1.166 | 1.940 | 1.177 |
| Arithmetic normalization replay | 0.176 | 0.150 | 0.172 | 0.152 |
| Scoped arithmetic replay | 1.373 | 1.038 | 1.382 | 1.032 |
| Nested scope export replay | 0.126 | 0.232 | 0.124 | 0.233 |

The small nested replay regressed. Congruence and predicate timings vary
substantially across fresh processes, including CPU time; recorded system
loads and allocation/GC profiles must accompany these numbers. The useful
sample savings are most apparent with two sorts and supplied roots. No claim
about the final benchmark matrix, larger LIA proofs, or competitiveness
follows. Raw per-run timings, process CPU/wall (including startup/imports),
source hashes, native profiles, commands, exit codes and assumptions are in:

* `/tmp/eunoia-proof-reuse-before2/`: eight supported baseline cases, each
  twice. Its overall exit is **1**, because the initially proposed extra LIA
  equivalence fails generated `not_equiv_elim2` derivation in both runs.
  The failure is retained and is not counted as a positive measurement.
* `/tmp/eunoia-proof-reuse-before-lia/`: the existing supported live bound
  conflict, twice, exit **0**. This supplies the table's LIA baseline.
* `/tmp/eunoia-proof-reuse-after3/`: all nine positives twice, main/helper
  audits, and controls, exit **0**. Every main export is proved with `Qed`.
* `/tmp/eunoia-proof-reuse-timing-summary.json`: derived medians above.

Every semantic/checker `.vo` hash matches across before/after metadata.
`theories/SMTCoq.vo` and `theories/tactics/Tactics.vo` were rebuilt with the
changed native plugin; their source files were not changed. All relevant
source and artifact revisions are recorded, rather than treating an old
native plugin as the candidate. The driver explicitly builds and hashes
`src/smtcoq.cmxs`, the backend `.cmxs`, and the test plugin `.cmxs`.

Separate instrumented runs at
`/tmp/eunoia-proof-reuse-input-{before,after}/` both exited **0**. They used the
original backend body and the candidate body with the same instrumentation,
interface, source goals and checker modules. The raw full-expression SHA-256
and every per-step table snapshot match exactly for abstract congruence,
repeated supplied hypotheses and scoped arithmetic. The expressions contain
the complete fuel/roots/source trace/witness arguments, not just a theorem
name or rule inventory. Full hashes and snapshots are retained in
`/tmp/eunoia-proof-reuse-input-comparison.json`.

| Instrumented case | Steps | First atom/form slots | Final slots | Added inside witness calls |
| --- | ---: | ---: | ---: | ---: |
| Congruence | 13 | 7 / 6 | 14 / 21 | 4 / 4 |
| Supplied roots | 16 | 9 / 7 | 22 / 29 | 8 / 8 |
| Scoped LIA | 7 | 11 / 8 | 11 / 12 | 0 / 3 |

Reifying generated results also grows tables between witness calls. These
counts distinguish that growth from producer-added auxiliary equalities.
They establish no general bound and do not change the producer. Instrumented
timings are excluded from the production table. Both source backups were
restored and the production native plugins rebuilt before final validation.

## Validation record and limits

The initial and candidate `dune build -j2 @install` commands exited **0**.
The latter's complete command/result is
`/tmp/eunoia-proof-reuse-candidate-smoke/build/command.json`. Focused
`dune build -j2` of `Proof.vo`, `Public.vo`, `Lia.vo` and `backend_tests.exe`
exited **0** (`/tmp/eunoia-proof-reuse-integration-build.log`). The restored
production backend's native tests exited **0**
(`/tmp/eunoia-proof-reuse-final-native-tests.log`), including solver resource,
malformed output and cleanup controls.

Final aggregate command (exit **0**):

```sh
python3 -B tools/eunoia-proof-reuse/verify.py \
  --profile-dir /tmp/eunoia-proof-reuse-after3 \
  --output /tmp/eunoia-proof-reuse-final-validation
```

`/tmp/eunoia-proof-reuse-final-validation/status.json` records all exact
commands, CPU/wall and exits: plugin build **0**, validation compilation
**0**, main assumption audit **0**, helper-body audit **0**, recursive kernel
check **0**. There are 17 proved exports and 15 saved certificate-body audits;
both dependency audits pass the unchanged baseline. The recursive check took
35.268 wall seconds (35.262 user, 0.191 system); every dependency and validation
`.vo` hash was unchanged. The compilation, including all private helper work
and rejection controls, took 34.575 wall seconds (34.303 user, 0.413 system).
The backend source SHA-256 is
`17e7ee41a311e72b168bfc8b7bef33d7cd474521f206ac69c2001a456a3e6b99`.

One additional focused diagnostic uses the exact integer transitive-congruence
theorem from the parent's completed
`/tmp/smtrocq-composed-runtime-witness-diagnostic/benchmark/runs/cvc5_eunoia/uf_transitive_congruence/1/case.v`:

```sh
python3 -B tools/eunoia-proof-reuse/run.py \
  --output /tmp/eunoia-proof-reuse-parent-transitive \
  --cases integer_transitive --timeout 30 --helpers
```

It exited **0**, closed with `Qed`, and passed main and saved-certificate
audits. Tactic wall/user/system were 21.526 / 21.612 / 0.045 seconds; `Qed`
was 0.086 / 0.087 / 0.000. Compiler process wall/user/system were
23.470 / 23.226 / 0.362. All helper work is included. This is one profiled
development probe under the original 30-second compiler cap, not a rerun of
the benchmark matrix or a controlled performance comparison with the parent's
unprofiled attempt. No positive source goal was removed or weakened.
Its separate recursive kernel check exited **0** in 42.208 wall seconds
(42.023 user, 0.241 system), with every `.vo` hash unchanged. The exact command
and hash comparison are in
`/tmp/eunoia-proof-reuse-parent-transitive/integer_transitive-1/kernel/status.json`.

Discarded attempts are retained: the first baseline driver timed out waiting
for an overlapping build; the first candidate smoke proof closed but its audit
incorrectly expected an exported helper name; another candidate run failed at
plugin loading after an interface documentation change left a consumer plugin
stale. None is reported as successful validation or a performance sample.
Later commands build every relevant native plugin explicitly. An initial
per-file recursive check passed congruence and predicate; it was stopped in
favor of the aggregate check to avoid rechecking identical dependencies once
per file.

The implementation adds no general soundness lemma. Main theorems use ordinary
`Print Assumptions`; the saved helper-body audits use the same Rocq dependency
walker and printer. Every dependency must belong to the existing 52-name
baseline. Fully quantified carriers (the original Quantified.23 regression
shape), two sorts with intermediate CompDec, repeated supplied proofs,
negative predicates, nested scope export, missing instances, false goals,
corrupt supported unused steps/witnesses, failed attempts, Undo and polymorphic
Section discharge are covered. No shared Dune stanza or tactic/theory interface
change is required. The new developer probes are explicit commands, not a
new default test alias; integration into a shared alias belongs to the parent.

Overall port completion, the public UF/LIA benchmark matrix, larger LIA timeout
resolution and any parent merge remain outside this child change.
