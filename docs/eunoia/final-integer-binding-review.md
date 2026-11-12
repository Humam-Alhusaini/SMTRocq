# Independent integer-binding and final proof-boundary review

Reviewed revision: **`45b3411f11ce60da4e51c4cf8260b0bd9bb29ca6`**, the
`smtrocq/cvc5-eunoia` integration of `93d11ee7f37f0eed129d58dc5ddbb303893d4bf6`.
Review branch: `t3/review-integer-binding` (initially `t3/218a03fc`).
Review checkout: `/home/charles/.t3/worktrees/SMTRocq/t3-218a03fc`.
Date: 2026-11-03. This is a new independent review of the changes since the
`7c2e21d` pin in `trust-boundary-review.md`, including `2e36fb4`, `53e2c32`,
and callback sharing in `26da5ad`.

**Findings: no new P0/P1/P2 issue identified in the inspected paths. The prior
P2 R1 legacy failure-fallback issue is resolved at this revision.** This is
bounded source review and targeted verification, not overall backend acceptance.
Only this document is added. Production files, shared tests, build stanzas,
and tactic files are unchanged. No delegation, dependency installation, network
access, push, PR, or GitHub comment was performed.

## Integer lowering and exact source binding

* `EunoiaAdapter.v:34–62` reconstructs application spines in their original
  order, recursively lowers each operand, and changes only `+`/`*` applications
  with at least three operands into a right-associated binary tree. It retains
  duplicates, signed literal spelling, every operand, and existing binary
  subtrees. It neither commutes nor sorts operands. Exhaustion returns `None`.
* `binds_spec` at `EunoiaAdapter.v:288–301` now says precisely that the bounded
  canonical clause encodes to some `u` and the raw source lowers to that same
  `u`. It no longer asserts equality with the unlowered source. This is a
  syntactic binding theorem; it does not prove an independent interpretation
  of arbitrary CPC arithmetic or an equivalence with Ethos normalization.
  `bind_terms_spec` retains exact premise count and order through `Forall2`.
* Type safety comes from the same existing SMTCoq tables: `encode_atom` checks
  bounds, structural ordering, `Atom.check_aux`, and the supported sort;
  `encode_literal` requires Boolean atoms; `tables_wf` checks
  `Form.check_form`, `Atom.check_atom`, and `Atom.wt`. Reserved names prevent
  user functions named `+`/`*` from being confused with these primitives.
  Lowering itself deliberately performs no typing or arithmetic evaluation.
* `EunoiaAdapter.v:482–501` passes the **raw** arguments and ordered premise
  terms to `CpcGenerated.derive`. The generated result must equal the raw
  payload result before its lowered clause binding is accepted. The backend
  retains these raw fields in `Payload` (`eunoiaBackend.ml:184–191`). The
  elaborator checks any printed conclusion against the generated term before
  reification (`eunoiaElaborate.ml:112–136`). Generated computation has not
  been replaced by a hard-coded CPC rule checker.

Independent `BindingProbe.v` has 31 compiled examples, including 128
operator/triple combinations over four distinct leaves, n-ary addition and
multiplication, retained left-associated binary trees, nine operand mutations,
four explicit negations, fuel exhaustion, and malformed types/arities.
An actual generated `refl` on `(+ n m n)` retains that raw term in its result.
The actual adapter accepts its raw payload and rejects replacing the payload
result with the equivalent lowered binary tree, even though that tree binds
to the same clause. Actual generated `scope` retains the raw endpoint term.

The partial type query still classifies a three-argument `-` as `Int`; this is
inherited behavior, not new support from this change. The probe confirms
`lower_arithmetic` leaves it untouched and it cannot bind to a binary atom.
Nullary/unary `+` and unary `*` also cannot bind; mixed Boolean/integer and
rational object operands fail. Metadata literal admission does not introduce
an object-level Real interpretation. No acceptance defect was demonstrated.

## Authoritative roots, explicit negations, and local candidates

`export` (`eunoiaBackend.ml:69–92`) now prints each authoritative singleton
root using `EunoiaAdapter.encode_clause`, rather than a legacy printer that
rewrites signed literals to unary minus. The same encoder supplies
`root_terms` in `prepare`. Imported assumptions must match those terms in
order before any proof step. Distinct roots cannot disappear when cvc5
deduplicates identical assertions: every original root claim/slot is retained.
The signed literal probe distinguishes `-3` from `(- 3)`; the live theorem
`((x + -3) - x =? -3) = true` closes with `Qed`.

`reify` (`eunoiaBackend.ml:96–114`) uses the same right fold for n-ary `+`/`*`
and calls the existing importer with `eqsym:false` and `preserve_not:true`.
`smtlib2_genConstr.ml:371–379` represents explicit double negations by the
existing `Fnot2`, preserving source syntax at the boundary. Local search
may emit `ImmFlatten` from an exact singleton root (`search.ml:317–332`);
its read dependency is recorded in `certificate.ml`, retained by local DAG
slicing, serialized, and recomputed by the existing small checker. Flattening
does not silently replace a CPC premise or split a disjunctive premise.

`search.ml:286–314` expands `Fiff`, `Fxor`, and `Fite` only for the untrusted
Micromega candidate producer. Its Boolean expressions match the existing
`LIA.build_hform` cases (`LIA.v:221–280`), and it emits `LiaMicromega` for the
**original** clause. Canonicalization precedes certificate generation. Any
traversal/variable-numbering mismatch can cause rejection, but successful
candidate production is not trusted: `EunoiaLocal.execute` recomputes the
existing checker result, checks bounds/freshness/expected output and rejects
failure fallbacks. The final tables are serialized after witness production.

The actual production gate probe passes 75 search cases, including explicit
positive/negative double negation, integer-gap and normalization iff,
disjunctive premises, reordered certificate clauses, and incorrect conclusions.
It serializes and evaluates every positive candidate, and rejects mutations
of roots, capacity, expected clauses, supplied premises/conclusions, and the
scaling Micromega evidence. This probe uses irrelevant interpretation tables
and establishes gate computation, not whole-proof table typing or CPC
acceptance. The separately compiled typed backend `Lia.v` establishes four
checked replay proofs and rejects altered coefficient, premise, conclusion,
root, missing Micromega certificate, and a bad unused arithmetic certificate.

## Every step, scope restrictions, and final theorem application

The elaborator processes all commands, including unused steps, before selecting
a live final conflict. The ordinary/scoped backend retains every such step;
local witness slicing removes candidate scratch operations only. Both core
runners continue after a conflict. `StepsProbe.v` independently appends a
supported generated `refl` after global and local conflicts: valid witnesses
are accepted, and replacing only the unused step's witness by an invalid one
rejects the whole trace in both locations. Thus these are not merely
unknown-rule rejection controls.

`EunoiaScopedAdapter.scope_eval_with` uses actual generated
`derive_assuming_with`, the encoded pushed literal, and the exact unguarded
endpoint clause. The runtime requires exactly the source rule's assumption
mode and premise arity. Only the semantic gate receives the guarded clause
`S.sort (Lit.neg assumption :: endpoint)`. Parent snapshots are restored
before exporting one fresh result. The compiled scoped tests and backend
`Proof.v` reject changed assumptions/polarities, endpoint substitution,
missing/extra premises, ordinary rules at pop, assumption rules as ordinary
steps, expired scope references, unguarded leakage, and invalid unused steps.
Nested scopes with essential exports also succeed through generated computation
and the concrete gate. `BindingProbe.v` separately checks generated rejection
of the two incorrect assumption modes.

The production flat/scoped theorem wrappers fix `EunoiaLocal.gate`; their
proofs discharge its `Atom.wt` requirement from the same checked table guard.
Their valuation is the existing `Atom`/`Form` interpretation. The raw syntax
binding does not replace this semantic proof obligation. The `checker_b`
wrapper constructs the opposite goal root itself; `checker_eq` checks the
signed `Fiff` and both children. The supplied-lemma path constructs root
validity from actual hypothesis proof terms under the opposite-goal assumption.

The `53e2c32` fix is preserved: `R.mk_tactic` obtains `Proofview.Goal.sigma`,
the backend pushes its universe context into the VM environment, and the
supplied-lemma path calls `refutation ~sigma` (`eunoiaBackend.ml:288–304,342`).
`Typing.type_of` therefore uses the actual goal sigma. The low-level API's
optional fallback remains `Evd.from_env`; callers with proof-local universes
must provide sigma, as documented. No trust bypass was added: accepted
checker computation is converted to `true` before constructing the VM cast,
and the final proof still goes through `Tactics.exact_check`. Diagnostic
recomputation is confined to rejection and cannot accept a proof.

Both quantified-carrier public regressions and the duplicate supplied-root
proof compile and pass recursive kernel checking. An independent live
`forall (A : Type) (HA : CompDec A) ...` negative-predicate transport proof
also closes with `Qed`, exercising explicit negations and the supplied-fact
path with a proof-local carrier. An independent false integer goal is rejected.

## Prior R1: independently verified resolution, severity P2 closed

`EunoiaBridge.v:63–67` now delegates to `EunoiaLocal.decode`, admitting only
supported operation shapes and exactly two resolution inputs. The gate at
lines 91–99 adds canonical bounded conclusions, referenced-literal bounds,
`result_supported`, and exact result equality. Only explicit `CTrue` may
certify the old true-clause fallback. Longer chains must expose every link.

All nine `EunoiaBridgeTests.v` controls were rebuilt and recursively kernel
checked here. In particular, failed weakening from `[4]` to `[0]`, failed
equality, and the failed-intermediate four-input chain reject; the exact
generated-adapter reproduction now returns `false`. Dedicated truth, identity
weakening, and valid binary resolution still accept. The legacy
`checked_checker_correct`, `EunoiaScope.table_checker_correct`, and
`EunoiaBridge.gate_correct` pass independent baseline-relative assumption
audits. No unresolved R1 acceptance path was found in either exported wrapper.

## Commands, provenance, and assumptions

All commands ran from the review checkout using the private wrapper. Retained
evidence directory: `/tmp/smtrocq-final-integer-binding-review-45b3411` (`r`
below). `commands.jsonl` contains exact expanded argv, cwd, exit codes and
log paths, including the two unsuccessful temporary probe setup attempts.
`source-hashes.json` records 81 reviewed source hashes checked against
`git show 45b3411:<path>`; uniquely mapped installed Rocq sources were compared
byte-for-byte. Objects were built in this checkout, not copied from the active
parent or UF/LIA children. No Logos or Ethos source was needed for this review.

```sh
env=/home/charles/code/friends/.toolchains/smtrocq-env
r=/tmp/smtrocq-final-integer-binding-review-45b3411
lib=_build/install/default/lib
theory=$lib/coq/user-contrib/SMTCoq

"$env" dune build -j2 @install \
  theories/checker/eunoia/EunoiaBridgeTests.vo \
  theories/checker/eunoia/EunoiaLocalTests.vo \
  theories/checker/eunoia/EunoiaScopedAdapterTests.vo \
  src/eunoia_backend/tests/integration/Proof.vo \
  src/eunoia_backend/tests/integration/Public.vo \
  src/eunoia_backend/tests/integration/Lia.vo
# 0; build.log
"$env" dune runtest -j2 src/eunoia_backend/tests src/eunoia_witness/tests
# 0; native-tests.log; 75 search cases and elaborator/solver controls

python3 -B tools/eunoia/regenerate.py \
  --output "$r/CpcGenerated.v" --manifest "$r/manifest.json"
cmp theories/checker/eunoia/CpcGenerated.v "$r/CpcGenerated.v"
cmp tools/eunoia/cpc-manifest.json "$r/manifest.json"
# all 0; identical 48 rules, 53 helpers, 35 includes, 561 excluded rules
python3 -B "$r/verify-extra.py"
# 0; pinned source/installed-source comparisons and strict-token checks

"$env" rocq c -Q "$theory" SMTCoq -Q "$r/probe" Review "$r/probe/BindingProbe.v"
"$env" rocq c -Q "$theory" SMTCoq -Q "$r/probe" Review "$r/probe/StepsProbe.v"
"$env" rocq c -I "$lib" -Q "$theory" SMTCoq -Q "$r/probe" Review "$r/probe/GateProbe.v"
"$env" rocq c -I "$lib" -Q "$theory" SMTCoq -Q "$r/probe" Review "$r/probe/LiveProbe.v"
# all 0; binding-probe.log, steps-probe-final.log, gate-probe.log, live-probe.log

"$env" rocq check -silent -Q "$theory" SMTCoq -Q "$r/probe" Review \
  Review.BindingProbe SMTCoq.checker.eunoia.EunoiaBridgeTests \
  SMTCoq.checker.eunoia.EunoiaLocalTests SMTCoq.checker.eunoia.EunoiaScopedAdapterTests \
  SMTCoq.eunoia_backend_tests.Proof SMTCoq.eunoia_backend_tests.Public \
  SMTCoq.eunoia_backend_tests.Lia
"$env" rocq check -silent -Q "$theory" SMTCoq -Q "$r/probe" Review \
  Review.LiveProbe Review.StepsProbe
# both 0; kernel-check.log and extra-kernel-check.log; no dependency-admission flags
python3 -B "$r/audit-probes.py"
# 0; probe-audit.log, exact expanded assumption-audit argv in commands.jsonl
git diff --check
# 0
```

`signature-hashes.json` independently records that all 35 manifest source
hashes match the privately installed cvc5 1.4.2 CPC directory. Forbidden-token
`rg` over Eunoia theories, backend, witness code and changed shared importer
returned 1 with no matches, as expected. No proof hole or new assumption was
introduced. The first two `StepsProbe.v` compilations exited 1 because the
temporary file omitted module imports and then string notation; corrected
imports compiled without changing production code or test expectations.

The assumption audits use the repository script and exact 52-entry baseline:

* `/tmp/smtrocq-final-integer-binding-audit-45b3411/summary.json`: compiler
  and audit exit 0; 24 declarations, including new binding specifications,
  legacy/local gates, concrete flat/scoped correctness, all four LIA replay
  proofs, quantified carriers, supplied roots, and essential scoped exports.
  The exact command is the `audit.log` entry in `commands.jsonl`.
* `/tmp/smtrocq-final-integer-binding-probe-audit-45b3411/summary.json`:
  compiler and audit exit 0; all 38 independently added probe examples/live
  proofs plus the legacy scoped wrapper. No new assumptions in either audit.

Each audit's assumption union is the existing 52-entry baseline, including
primitive integer operations, their `Uint63Axioms` specifications, and
`ProofIrrelevance.proof_irrelevance`. This is not an axiom-free claim.
No production soundness lemma was added in this review. Every temporary probe
theorem was included in `Print Assumptions`; the two temporary live soundness
proofs also print assumptions directly in `LiveProbe.v`.

## Limits and safe performance opportunities

This review does not cover subsequent UF/LIA-child commits or establish the
complete meaningful QF_UF/QF_LIA acceptance suites. No whole benchmark or full
repository `dune runtest` was run. Resource exhaustion, unsupported rules/sorts,
Boolean equality as a function argument, and other coverage gaps can still
reject valid proofs. The prior documented structural-order difference from
Ethos is unchanged; this review adds no equivalence theorem for it. Source
binding and all local gates remain necessary regardless of solver success.

Public proof latency has not been benchmarked here. Source-level opportunities
for a separate measured change are sharing final immutable table checks and
type queries across steps, sharing structurally equal closed Rocq terms, and
memoizing untrusted Micromega/search candidates for identical local inputs.
Any cache needs the complete relevant table/environment/fuel/input identity;
every original CPC step must still undergo generated derivation, source
binding, and checked semantic validation. The existing cheap CNF/EUF-first
ordering can also be profiled before expanding arithmetic iff candidates.
No performance change is implemented or speedup claimed here. Coordinator
integration, later revisions, final suites and benchmark acceptance remain
incomplete and outside this review's conclusion.
