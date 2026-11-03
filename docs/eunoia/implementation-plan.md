# cvc5 / Eunoia implementation milestones

Status: implementation in progress. This document does not claim an operational
backend or a completed soundness proof.

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
