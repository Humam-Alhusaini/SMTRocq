# cvc5 / Eunoia implementation milestones

Status: implementation in progress. A checked `cvc5_eunoia` tactic runs live
UF and integer arithmetic integration goals. Separate complete UF and LIA
milestones are verified and registered; composed final validation, larger
benchmark coverage and measured efficiency remain incomplete.

## Required outcome

A CPC signature-generated reflective checker for cvc5 proofs, reusing SMTCoq's
`State`, `Terms` (`Atom` / `Form`), EUF, and LIA semantics and checkers. The
initial end-to-end target is QF_UF and QF_LIA. Every proof step must be checked;
unknown rules, unsupported constructs, missing premises, and altered input
assumptions must fail closed. No solver result is a proof by itself.

## Parallel ownership

* Architecture survey: `docs/eunoia/smtcoq-architecture.md`.
* Logos / CPC survey and design: `docs/eunoia/logos-design.md`.
* Private solver provisioning and CPC fixtures: `scripts/eunoia/`, fixture data.
* Signature compiler: `tools/eunoia/`, generated Rocq syntax and rule evaluator.
* Reflective checker: `theories/checker/eunoia/`, excluding generated syntax.
* UF: coverage inventory and reusable verified EUF bridge lemmas.
* LIA: coverage inventory and reusable verified LIA bridge lemmas.
* Benchmarks: `benchmarks/eunoia/`, with machine-specific results outside Git.

The coordinator owns shared dune files and tactic integration. Children may
supply patches or isolated new stanzas for these, but should avoid modifying
shared files until the integration interface is settled.

## Integration contract

The generator derives executable rule definitions and side conditions from the
actual CPC `.eo` signature, including its includes and helper programs. A rule
name inventory or manually implemented rule switch does not meet this contract.
Generated computation alone does not establish semantic soundness. Rule results
must be related to the existing `Atom` / `Form` interpretation by kernel-checked
proofs or verified small-checker certificates. A semantic certificate gate is
acceptable only if it checks each derived result against the exact premises and
conclusion; it cannot replace the CPC proof with an independent solver run.

The core should expose a generic checked-step interface over existing `S.t`,
prove state preservation and refutation soundness, and make premise and root
binding explicit. Generator and core owners should document their concrete
interfaces early. Neither owner should create a second SMT-LIB semantics.

## Initial evidence (2026-11-03)

* Base branch: `smtrocq/cvc5-eunoia`, initial commit `c0bd765`.
* Wrapper: `/home/charles/code/friends/.toolchains/smtrocq-env`.
* `smtrocq-env dune build theories`: passed after private dependencies finished
  installing. A first overlapping build had failed while they were incomplete.
* `smtrocq-env dune build -j2`: completed with exit code 0, including existing
  benchmarks. Log: `/tmp/smtrocq-baseline-full-build.log`.
* `smtrocq-env dune runtest`: completed with exit code 0. Its log is retained
  at `/tmp/smtrocq-baseline-tests.log`; existing LFSC hypothesis warnings are
  present. This is regression evidence, not a soundness claim for a new backend.
* Logos source surveyed at `89df5909b0e9aabb936b68ee95c75a18f609db7a`,
  `/tmp/smtrocq-logos`. Issue <https://github.com/cvc5/logos/issues/485> was read;
  the web rendering showed the performance question and no maintainer reply.
* cvc5 1.4.2 static binary installed privately at
  `/home/charles/code/friends/.toolchains/cvc5-1.4.2/cvc5-Linux-x86_64-static/bin/cvc5`.
  Its version reports commit `282d5e0`. The matching signature is at
  `/home/charles/code/friends/.toolchains/cvc5-1.4.2/cvc5-cvc5-1.4.2/proofs/eo/cpc/Cpc.eo`.
* `cvc5 --dump-proofs --proof-format=cpc unit-tests/files/uf4.smt2` returned
  `unsat` and a CPC proof, retained at `/tmp/smtrocq-uf4.cpc`.

## Completion audit

Build and run existing and new tests through the private wrapper. Audit main
soundness and tactic correctness with `Print Assumptions`. Inspect the diff for
forbidden proof holes or added assumptions. Benchmark checked tactics, reporting
solver-only timings separately. Do not claim Lean-SMT or Sledgehammer comparisons
without compatible measured or published evidence. Make small local commits;
never push or publish. The final PR draft belongs at the user-requested path
outside this repository and must describe actual verified coverage and limits.

## Foundation integration evidence

All eight initial child jobs, the strict proof reader, and the structural
term/clause adapter have been merged. Their reports document exact source pins,
commands, coverage limits and retained logs. The initial generator supports 13
rules, not the complete UF/LIA trace surface. The concrete semantic bridge
supports one existing checker operation per generated result. The remaining
generator expansion, local certificates, scoped checker, witness production
and tactic pipeline are dependent implementation work, not optional polish.

At `227a3f8`, both `smtrocq-env dune build -j2` and `smtrocq-env dune runtest -j2`
completed with exit code 0. Logs are `/tmp/smtrocq-foundations-full-build.log`
and `/tmp/smtrocq-foundations-full-tests.log`. After the adapter merge,
`dune build @install -j2` also passed. The coordinator's assumption audits passed
for four core/bridge declarations, nine UF/LIA bridge declarations and all eight
adapter declarations, against `baseline-assumptions.txt`. Their full outputs
and JSON summaries are in `/tmp/smtrocq-integrated-{core,bridges,adapter}-assumptions/`.
These checks do not yet audit a tactic correctness lemma or an end-to-end CPC
proof, because that integration is still unfinished.

The Logos survey retrieved the two issue #485 replies through the comments API;
the initial web rendering had omitted them. See `logos-design.md` for the exact
comments and optimization suggestions. The old-backend measurements and their
limits are retained at `/tmp/smtrocq-eunoia-baseline-20261103-946ad9fd/report.txt`.
The local PR draft at the requested path has been updated with these milestones,
the measured baseline table, and explicit unfinished completion requirements.

## Live integration milestone

The public `cvc5_eunoia` tactic now invokes the private cvc5 1.4.2 runner,
strictly reads CPC output, computes generated conclusions, constructs local
certificates, and applies the concrete reflective checker correctness theorem.
`unit-tests/eunoia_tactics.v` contains live integer reflexivity and function
congruence proofs and two false-goal rejection controls. The audit in
`/tmp/smtrocq-two-live-goal-assumptions/summary.json` passed for both exported
proofs without additional assumptions. This is a smoke milestone, not the
required meaningful QF_UF/QF_LIA suite.

The merged runtime currently generates 30 rules and 34 helpers from the pinned
35-file signature closure. The multi-operation semantic gate checks every
generated result against its exact premises. Its explicit `CTrue` operation
can certify the true clause; all other operations still reject that clause as
a checker fallback. Equality reification preserves source operand order.

Exact arithmetic literal primitives and the concrete generated scoped adapter
have been merged. Their 133 and 59 computation examples respectively are now
registered in the test alias. The arithmetic module is not yet wired into
generated arithmetic computation, and the production backend still rejects
scoped proofs. The backend replay suite is also registered: four checked replay
proofs plus a live proof, with invalid output, an invalid semantic certificate,
and an invalid unused step rejected before that live proof succeeds.

The integrated build command was:

```sh
/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2 @install \
  src/eunoia_backend/tests/integration/Proof.vo \
  theories/checker/eunoia/EoArithmeticTests.vo \
  theories/checker/eunoia/EunoiaScopedAdapterTests.vo
```

It exited 0; output is in `/tmp/smtrocq-integrated-arithmetic-scope-build.log`.
The three scoped checker correctness theorems and the new live/rejection replay
theorem passed the integrated assumption audit in
`/tmp/smtrocq-scoped-replay-integrated-assumptions/summary.json`.

The first new-backend benchmark is a development diagnostic, retained in
`/tmp/smtrocq-first-cvc5-eunoia-live-benchmark/`. Only one of twelve positive
cases checked; both false controls were rejected. The remaining cases expose
missing generated arithmetic normalization, Boolean implication, metadata
syntax/type queries, and scope integration. No performance or competitive
coverage claim follows from this run. In particular, the nominal UF benchmark
cases use integer carriers and can invoke arithmetic normalization in cvc5;
an abstract-carrier UF suite is still needed.

The first full `dune runtest -j2` after this integration exposed missing Python
input dependencies in the generator's Dune alias (`rules.txt`, the replay
module, manifest and provenance inputs). The coordinator added those declared
dependencies. The targeted generator alias then passed all 31 tests, and the
subsequent full regression command exited 0. Logs are
`/tmp/smtrocq-generator-dune-regression.log` and
`/tmp/smtrocq-corrected-generator-full-runtest.log` respectively. A failed first
run is not reported as a successful full regression.

## Generated arithmetic and scoped backend integration

The LIA source computation and scoped backend branches are merged at
`604b951` and `e246dcd`. The generated snapshot now has 48 rules and 53 helpers;
all 962 steps across 28 original/reduced UF/LIA fixtures compute. This is
signature-computation evidence, independently of semantic checking. The
production backend now builds nested traces with exact guarded discharge and
preserves every authoritative root when cvc5 deduplicates source assertions.
The adapter's default primitive configuration and the tactic's module loading
were wired in `2dc18f5`; the backend consumes the complete generated signature
namespace inventory. No proof data chooses native hooks.

The combined `dune build -j2 @install` with backend `Proof.vo` and `Public.vo`
exited 0 (`/tmp/smtrocq-generated-lia-scoped-backend-build.log`). The default
generator test alias now runs the standalone compilation and independent
kernel checks in addition to its 39 Python tests. Its integrated invocation
`smtrocq-env dune runtest -j2 tools/eunoia` exited 0; output is retained in
`/tmp/smtrocq-generated-lia-default-runtest.log`. Eight concrete scoped/tactic
correctness and live public declarations passed the assumption comparison in
`/tmp/smtrocq-generated-scoped-integrated-assumptions/summary.json`.

The benchmark workload now includes abstract carriers, alongside its original
integer-carrier UF and LIA goals. Its first diagnostic exposed a proof-local
universe anomaly when a carrier is quantified inside the theorem; Section
carrier tests did not expose that bug. The exact commands and failed proofs
are retained in `/tmp/smtrocq-abstract-uf-development-benchmark/`.
Coordinator fix `53e2c32` retains the actual goal evar map during explicit proof
typechecking. The original fully quantified goal now closes and its assumption
audit passes; see `/tmp/smtrocq-goal-universe-context-assumptions/summary.json`.
All six abstract-carrier benchmark goals then checked for both cvc5 and veriT
in `/tmp/smtrocq-abstract-uf-universe-fixed-benchmark/`. The carrier was not
changed to avoid the regression.

The live abstract UF suite has a separate explicit-double-negation binding
failure in negative predicate transport. Shared reifier commit `fbfbe26` adds
an optional exact-negation mode using the existing `Form.Fnot2` representation;
`smtrocq-env dune build -j2 src/common` exited 0. Production wiring and semantic
witness validation were integrated in `45b3411`: the backend preserves explicit
negations and the local producer emits checked `ImmFlatten` operations from
exact singleton roots. The original negative-predicate goal now closes with
`Qed` and adds no assumptions
(`/tmp/smtrocq-negative-predicate-assumptions/summary.json`). The full 22-goal
file has since passed: all 22 public-tactic positive theorems close in one file,
both false controls reject, and all 22 exported-theorem audits add no assumptions.
The child evidence is `/tmp/smtrocq-live-uf.rjFR6E/assumptions/summary.json` and
`/tmp/smtrocq-uf-complete-suite.log`. Integration `51847bb` merges the suite;
`13161ee` registers it in the default unit-test theory. Final composed regression
still must pass after all pending LIA and performance changes.

The same integration adds deterministic right-fold lowering for n-ary integer
`+`/`*` while retaining each raw source payload. The generated rule computation
and local semantic gate both remain mandatory; see the exact contract in
`adapter-interface.md`. Five main/scoped/arithmetic replay assumption audits
passed in `/tmp/smtrocq-local-lia-negation-core-assumptions/summary.json`.
Targeted backend, witness and theory tests passed, including 75 native witness
cases (`/tmp/smtrocq-local-lia-negation-targeted-tests.log`). The four source
arithmetic replays are deliberately labeled replays, not live LIA acceptance.

The independent trust-boundary review found permissive failure fallbacks in the
legacy one-operation bridge, without demonstrating a false theorem. Coordinator
fix `2e36fb4` rejects those fallbacks and requires explicit binary resolution
links. Nine new bridge regressions, existing scoped/backend tests, five assumption
audits and recursive kernel checking passed. The original finding and exact
resolution evidence remain in `trust-boundary-review.md`.

## Callback sharing

The local gate and scoped evaluator now bind immutable table guards outside
their changing per-step arguments. This permits reuse when they are passed as
partially applied callbacks. The Boolean checks and every source/local proof
step are preserved. `/tmp/EunoiaGateSharingRefinement.v` proves equality with
the previous gate for every table, premise list, conclusion and witness by
`reflexivity`; its compilation exited 0 after correcting the temporary file's
loadpath and implicit-argument invocation.

The integrated build and existing local/scoped regression targets exited 0
(`/tmp/smtrocq-gate-hoist-build.log`), and four concrete correctness audits
added no assumptions (`/tmp/smtrocq-gate-hoist-assumptions/summary.json`).
Three live congruence repetitions before and after all closed with `Qed`.
Their commands, revisions, timing rows and assumptions are retained in
`/tmp/smtrocq-gate-hoist-before/` and `/tmp/smtrocq-gate-hoist-after/`.
These small sequential probes ran alongside other jobs and establish no
competitive speed claim. Final latency comparisons still need the complete
integrated backend and the same versioned workload for each solver.

## Live LIA and integer-tightening integration

`72bbd45` merges the LIA child `46cecc0`: fourteen actual integer proofs and
one mixed UF/arithmetic proof, two false controls, six corrupted-proof controls,
75 local-gate cases, 29 baseline assumption audits, and independent recursive
kernel checking passed in that child's frozen validation. Exact commands and
exits are `/tmp/eunoia-lia-suite/final-status.json`. The assumption audit is
`/tmp/eunoia-lia-frozen-assumptions/summary.json`; imported proof artifact hashes
were unchanged. `c79eeba` registers `unit-tests/eunoia_lia.v` in the unit-test
theory. Those uncapped correctness runs do not establish the benchmark time limit.

The merge preserves the actual goal sigma, propagates newly checked constraints
through Proofview and the optional builder sigma reference, and retains the
transparent default-fuel constant from `3dd364d`. The latter represents the
same bound of 10000; it does not change evaluator behavior or resource limits.

`e2704cb` merges actual-signature `arith-geq-tighten` support: 49 rules,
53 helpers and 560 explicitly excluded rules. All 994 source steps across
29 fixtures compute, including the exact 32-step strict-shift capture.
Forty-two Python tests, 27 new computation examples, independent kernel checks
and 28 closed assumption reports passed. See
`tools/eunoia/STRICT-SHIFT-VALIDATION.md` and
`/tmp/smtrocq-strict-shift-handoff.json`. Semantic acceptance of the unchanged
live strict-shift goal still needs verification after this merge.

The frozen parent checkpoint `f965e57` passed full `dune build -j2`, full
`dune runtest -j2`, 33 assumption audits including all 22 UF exports, and recursive
kernel checks; exact commands and exits are in
`/tmp/smtrocq-registered-uf-full-validation/status.json`. Composed UF/LIA and
new-generator validation is running separately under
`/tmp/smtrocq-integrated-lia-tightening-validation/`.

## Benchmark result integrity

The harness requires the fresh proof artifact, successful `Qed`, parsed tactic
and `Qed` timings, and an assumption report contained in the existing baseline.
Scoped imports close before printing, preserving qualified assumption names.
Unknown or unparsed dependencies do not count as solved. All fourteen harness
tests pass, including unknown-dependency rejection and detached solver cleanup.
The same actual congruence goal closed for all three backends with exactly the
allowed 52 assumptions in
`/tmp/smtrocq-benchmark-assumption-congruence-smoke/results.json`.

## Checked-certificate and Boolean UF integration checkpoint

At frozen `4f87e02`, private toolchain verification, `dune build -j2 @install`,
full `dune build -j2`, and forced full `dune runtest -j2` exited 0. Fresh copies
of the unchanged UF22 and LIA15 suites independently compiled with exit 0.
All 65 main/helper/export assumption audits and all 37 saved checker-certificate
body audits matched the existing baseline. Recursive kernel checking exited 0
in 87.099 seconds, with no imported artifact changes. Exact commands and logs:
`/tmp/smtrocq-reused-certificate-checkpoint/status.json`.

That driver's final whitespace check exited 2 on one upstream license-notice
trailing space; it did not mark the checkpoint fully verified. Commit `83c0ee4`
removes that space and clarifies historical signature provenance. All 35 `.eo`
SHA256 values still match the manifest, and the full branch diff now passes
`git diff --check`. Final composed token/build/proof audits remain required.
The independent bounded certificate-reuse review is in
`certificate-reuse-review.md`, with invalid-body rejection, rollback, assumption
and recursive kernel evidence; it found no new P0–P2 issue in its stated scope.

The unchanged 18-positive workload diagnostic at `4f87e02` checked 12 positives
(10/12 UF, 2/6 LIA), timed out on six, and rejected both false controls. Its
exit 1 and all raw proofs, timings, load metadata and diagnostics are retained
at `/tmp/smtrocq-certificate-reuse-workload-diagnostic/`. This is not the final
matched comparison or an efficiency-bar claim. Solver granularity probes at
`/tmp/smtrocq-proof-granularity-investigation/` found incomplete proofs in macro,
rewrite and theory-rewrite modes; DSL modes retained the complete proofs.
No proof-checking flags were relaxed.

The typed Boolean congruence integration retains every existing local operation
and adds a checked conditional clause operation. Its child checked 95 typed
native/gate cases, all original UF22/LIA15 proofs, and eleven additional public
Boolean UF positives with three false controls. Baseline audits and recursive
kernel checks passed; see `boolean-uf-integration.md`. Commit `75af686` registers
its public suite and theory tests. The parent composed Boolean/Local build and
public Boolean suite target also exited 0:
`/tmp/smtrocq-integrated-boolean-uf-build.log` and
`/tmp/smtrocq-boolean-integer-source-integration.log`.

Generated integer-cast source support is integrated by `055ae6e`: 51 selected
rules, 53 helpers, 47 Python tests, 1,158 computed source steps in 32 actual
captures. All original 994 steps remain. Its 61 additional assumption audits
were closed under the global context; independent kernel checks passed. See
`integer-cast-signature-coverage.md`. This is source computation evidence;
faithful raw-term metadata/binding and integer-only semantic embedding remain
necessary for live parity/coefficient-bound acceptance.

The composed `d56e85c` targeted regression (`dune runtest -j2` over the Eunoia
checker, backend, witness, generator and table-summary directories) exited 0:
`/tmp/smtrocq-boolean-integer-composed-runtest.log`. Added-source forbidden-token
and full-diff whitespace checks passed; the raw diff audit retains 59 matches
for review in `/tmp/smtrocq-current-forbidden-token-audit-d56e85c.json`.

A further integrated audit passed for 94 declarations, all eleven public Boolean
proof bodies and six saved rollback-control certificate bodies. Independent
recursive kernel checking exited 0 in 43.846 seconds, with no artifact changes:
`/tmp/smtrocq-integrated-boolean-audit-d56-explicit/status.json`. Two initial
setup failures are retained: overlapping build/install mappings, then missing
unit-test mappings. The audit CLI's explicit `--build-loadpaths` mode avoids
combining both library trees; defaults remain unchanged. These checks supplement
the prior full/fresh UF22/LIA15 checkpoint; final all-feature acceptance is pending.
