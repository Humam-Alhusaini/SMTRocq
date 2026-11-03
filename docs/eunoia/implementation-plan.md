# cvc5 / Eunoia implementation milestones

Status: implementation in progress. A checked `cvc5_eunoia` tactic runs live
smoke and UF integration goals; the complete UF/LIA acceptance suites and benchmarks are
still incomplete.

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
The active backend job owns that fix; changing the benchmark to avoid the
quantified carrier is not an acceptance solution.

The live abstract UF suite has a separate explicit-double-negation binding
failure in negative predicate transport. Shared reifier commit `fbfbe26` adds
an optional exact-negation mode using the existing `Form.Fnot2` representation;
`smtrocq-env dune build -j2 src/common` exited 0. Production wiring and semantic
witness validation remain with the active backend job. The other twenty UF
cases have separate checked probe evidence from the UF child, but the complete
file, audits and final regression still must pass before it is accepted.
