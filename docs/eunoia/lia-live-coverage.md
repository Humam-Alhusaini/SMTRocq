# Checked live integer arithmetic: child integration report

This is an implementation milestone, not completion of the cvc5/Eunoia port.
The public tactic runs the actual cvc5 CPC derivations and existing SMTCoq
semantic gates. Unsupported valid goals are recorded separately from proofs.

Coordinator integration `72bbd45` merges this milestone and retains the
sigma-reference API, returned constraints, and the unchanged default-fuel helper.
`c79eeba` registers the suite in `unit-tests/dune`; the registration obligations
below describe the original child handoff. The independently generated
`arith-geq-tighten` declaration is now included by `e2704cb` (49 rules in total).
Its source computation passes, while live semantic acceptance and larger-case
performance remain subject to the coordinator's composed validation.

## Source pins and ownership

The child branch is `t3/eunoia-lia-acceptance`, based on
`2dc18f52dc78331fe6be81604905a715ac17b9ab`. Local milestones:

* `b7896be`: carry proof-local universe declarations and constraints into the
  kernel environment used by VM reduction; forall-carrier regressions.
* `b8de5bc`: cherry-pick coordinator `fbfbe26`, the shared optional
  `Smtlib2_genConstr.make_root ~preserve_not` flag.
* `93d11ee`: exact root export, explicit source negations, checked integer
  n-ary lowering, metadata validation, generic local certificates and bad
  arithmetic proof replays.
* `3732a17`: definitionally equivalent callback guard sharing in adapter
  `typeof` and `eval_with`.
* `5865843`: correct the qualified reference to the exact metadata validator.
* `d4e737e`: preserve the actual goal sigma in the explicit refutation
  typecheck, and pass its returned constraints to Proofview before exact checking.
* `59ff015`: quoted metadata boundaries, scoped arithmetic, and integer-carrier
  UF regressions.
* `40858c2`: merge parent `2e36fb4`, including callback guard sharing
  `26da5ad`, legacy bridge hardening, and the parent universe regression.
  Equivalent sigma conflicts retain the child implementation, which returns
  constraints through Proofview and optional builder references.

cvc5 is the private 1.4.2 binary, git `282d5e0`, at
`/home/charles/code/friends/.toolchains/cvc5-1.4.2/cvc5-Linux-x86_64-static/bin/cvc5`.
The installed and vendored `Cpc.eo` entrypoints both hash to
`d13767eb873649c9f40482c99242c42081cf25308962f11c1981ce8e878770ad`.
The compiler uses the existing 35-file pinned closure and generated runtime;
this child changes neither selection nor generated source. Neither Logos nor
Ethos was executed or modified for this work. Their existing source contracts
are documented in the linked implementation notes.

The child owns backend/witness source, `EunoiaAdapter.v`, the isolated backend
integration test stanza, the new public LIA test source, and this report.
The coordinator must register `eunoia_lia` in `unit-tests/dune`. Main dune,
public tactic wiring, core/local/scoped theories, and generated runtime remain
coordinator-owned. No gate record, callback signature or primitive API changed.
The exported OCaml `export` adds an optional proof environment; existing
callers remain compatible, and production supplies its current environment.
The proof-building APIs also accept an optional sigma reference and return
explicit typechecking constraints through it. Tactic callers preserve their
actual sigma rather than replacing it with `Evd.from_env env`.

## Actual failures before fixes

All six LIA benchmark statements from `benchmarks/eunoia/cases.json`, originally
from `unit-tests/verit_tactics.v`, were attempted with the public tactic.
Exact commands, inputs and exits are retained in
`/tmp/eunoia-lia-live/before/results.json` and its adjacent `.v`/`.log` files.
The repeat in `/tmp/eunoia-lia-live/lia-before-complete/` has all six results;
a first overlapping-build probe in `lia-before/` had three import failures
and is not acceptance evidence.

| Goal | First relevant failure |
| --- | --- |
| disjunctive bounds | `@p5 arith-leq-norm`, no local witness |
| equality bound | `@p8 arith_poly_norm_rel`, no local witness |
| integer gap | `@p3 arith_poly_norm_rel`, no local witness |
| strict shift | `@p20 arith-geq-tighten`, generated derivation rejected |
| inconsistent bounds | `@p1`, authoritative root/source syntax mismatch |
| two-sided bound | `@p4 arith_poly_norm_rel`, no local witness |

Expanded failures are in `/tmp/eunoia-lia-live/lia-after.log` and
`lia-lowered.log`. The exact integer strict-shift arguments are
`(+ op_1 (* -1 op_0))` and `1`, with no premises. A fresh actual source proof
for equality-bound is retained as
`/tmp/eunoia-lia-live/equality-bound.{smt2,cpc}`. Its source `@p18 cong` uses
`@p17` and `@p10` to rewrite ` (= (- op_0 3) 7)` to
`(= (+ -3 op_0) 7)` inside a Boolean equality. That later failure exposed the
certificate-ordering bug; the corrected public proof passes.

Additional UF regressions exposed loss of explicit double negation and
missing proof-local universes. The original forall-carrier reproduction and
its exact command/exit are in
`/tmp/eunoia-lia-live/ForallCarrier.{v,json,log}`. It passed with checks enabled.
The negative-predicate forall-carrier proof also passed in
`/tmp/eunoia-lia-live/final/predicate_negative.{v,vo,log}`.

## Checked representation and local proof construction

Root export now computes the adapter's own encoding. It preserves canonical
signed literal `-3`; the legacy SMT-LIB printer changed it to `(- 3)`, a
different CPC tree. Ordered roots and duplicate claims are preserved.

The backend calls the shared importer with both `~eqsym:false` and
`~preserve_not:true`. Explicit double negations become existing `Form.Fnot2`
nodes. The generic witness language now exposes the existing checked
`Checker_Ext.ImmFlatten` operation. A candidate may use this operation to
normalize a singleton local root, with its explicit read slot and exact
expected result. Every original local root claim remains present.

Integer `+` and `*` with three or more operands have no n-ary integer Atom
constructor. The adapter's fuel-bounded `lower_arithmetic` checks a fixed
right-fold representation using existing binary integer atoms. It preserves
operand order, duplicates, and every explicit binary subtree. The OCaml
reifier produces the same fold. `binds_spec` and `bind_terms_spec` explicitly
state this checked lowering relationship; they do not claim that the binary
encoding can recover a unique source arity. Original source argument,
premise and result trees remain in every payload. Generated derivation still
compares the exact original result tree before binding its lowered clause.
No operands are sorted or canceled at this boundary. Malformed types, unknown
names, changed operands and insufficient fuel continue to reject. Four kernel
computation examples exercise n-ary order/duplicates, binary preservation and
exhaustion. Semantic acceptance is still the existing per-step local gate.

Micromega candidate generation supports arithmetic-shaped Boolean equality,
xor, ite and double negation by expressing its input using the very same
Boolean expansions as the existing kernel `LIA.build_hform`. The emitted
certificate still names the original clause. The candidate clause is sorted
before evidence generation, ensuring the kernel sees its exact literal order
and variable numbering. Cheap CNF/EUF candidates run before arithmetic
expansion, avoiding unnecessary arithmetic work on congruence steps. Whole
disjunctive premises remain whole formulas; no disjunct is assumed alone.
Existing clause, formula, term, resolution and theory-round limits remain.

Rational and decimal proof-source metadata are admitted only when the loaded
`EoArithmetic.EoArithmetic.normalize` accepts their exact spelling. The
spelling is retained, including its Real literal category. The same validator
rejects numeric declaration/binder names, including quoted numeric identifiers.
This adds no Real Atom constructor or Real object interpretation. Real object
terms, `to_real`, `to_int` proof terms and unsupported rules still fail closed.

## Replay rejection and kernel checks

`src/eunoia_backend/tests/integration/Lia.v` exports five checked proofs and
runs `Print Assumptions` on each. Its candidates use actual generated
`arith_poly_norm` and `arith_mult_neg`, the production witness search, and the
concrete semantic gate. Six source/evidence mutations reject:

* changed polynomial coefficient;
* changed premise occurrence;
* changed claimed conclusion;
* changed authoritative root;
* missing necessary Micromega evidence for multiplication by `-2`;
* the same corrupt evidence on an unused supported arithmetic step.

The last two deliberately use a nontrivial coefficient. Replacing a genuinely
empty valid certificate by another empty list is not rejection evidence.
Source commands and unused steps are all visited, independently of local
resolution-DAG pruning.

The final native suite has 75 cases, including explicit double-negation,
integer-gap iff, normalization iff, sum bounds, reordered certificate clause,
whole disjunctive premise and false arithmetic controls. The real local gate
replayed all 75 cases and rejected its mutations. Logs:

* `/tmp/eunoia-lia-native-final.log`;
* `/tmp/eunoia-lia-gate-final.log`;
* `/tmp/smtrocq-witness-probe.4rvw2U/` (complete typed VM gate replay).

The full wrapper build and the backend replay build both exited 0:

```sh
/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2 @install
/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2 \
  src/eunoia_backend/eunoia_backend.cmxs \
  src/eunoia_witness/eunoia_witness.cmxs \
  src/eunoia_backend/tests/integration/Lia.vo \
  src/eunoia_backend/tests/integration/Public.vo
/home/charles/code/friends/.toolchains/smtrocq-env dune runtest -j2 \
  src/eunoia_witness/tests src/eunoia_backend/tests
bash src/eunoia_witness/tests/verify-local-gate.sh \
  "$PWD/theories/checker/eunoia/EunoiaLocal.v"
```

The full build log is `/tmp/eunoia-lia-full-build.log`; the successful replay
log is `/tmp/eunoia-lia-linked-build2.log`. Targeted builds must include the
backend and witness `.cmxs` files: building only `src/smtcoq.cmxs` can leave
findlib-loaded dependency libraries stale. Abandoned overlapping diagnostic
runs and their timeouts are not final acceptance evidence.

The ten-declaration assumption audit passed against the existing baseline:
`/tmp/eunoia-lia-bridge-assumptions-final/summary.json`. It includes both
forall-carrier proofs, the original four LIA replay proofs, the changed binding lemmas,
`eval_with_binding`, and `checked_checker_correct`. The full command is in that
JSON. No additional assumptions were found. Recursive kernel rechecking also
exited 0, without admission flags:

```sh
/home/charles/code/friends/.toolchains/smtrocq-env rocq check -silent \
  -Q _build/install/default/lib/coq/user-contrib/SMTCoq SMTCoq \
  SMTCoq.eunoia_backend_tests.Public SMTCoq.eunoia_backend_tests.Lia \
  SMTCoq.checker.eunoia.EunoiaAdapter
```

Its log is `/tmp/eunoia-lia-kernel.log`. No new soundness lemmas or assumptions
were introduced; changed binding lemmas retain their `Print Assumptions` calls.

## Remaining live coverage

The new public source `unit-tests/eunoia_lia.v` has fifteen positive
independent goals (fourteen LIA goals and one mixed UF/LIA goal) and two false
controls. It includes all three successfully
checked benchmark cases (equality-bound, integer-gap, two-sided-bound),
unit/nonunit contradictions, addition/subtraction identities, coefficient
normalization (including negative coefficients), negative bounds, a sum of
inequalities and a scoped Boolean comparison. The mixed goal proves
`f (x+y) = f (y+x)` through arithmetic normalization and UF congruence.
Its reference solver capture `/tmp/eunoia-lia-live/uf-arithmetic.{smt2,cpc}`
contains `arith_poly_norm` at `@p4` followed by two `cong` steps. The pure
UF benchmark in `Public.v` also passes, but its reference capture contains
no polynomial-normalization rule; that benchmark alone is not evidence for
the mixed path. Individual successful proof
artifacts are in `/tmp/eunoia-lia-live/{pilot,final,remaining,priority}/`.
The complete standalone suite and its final audit are in
`/tmp/eunoia-lia-suite/`. The coordinator must register the new module in
the shared `unit-tests/dune`; this child does not edit that file.

The actual new-backtrace `Quantified.v` reproduction also compiles after
`d4e737e`, without rewriting it into a Section. Exact command (exit 0):

```sh
/home/charles/code/friends/.toolchains/smtrocq-env rocq c -bt \
  -I _build/install/default/lib \
  -Q _build/install/default/lib/coq/user-contrib/SMTCoq SMTCoq \
  /tmp/eunoia-lia-sigma/Quantified.v
```

Its output is `/tmp/eunoia-lia-sigma/compile-fixed.log`. The dependent
`src/smtcoq.cmxs` and backend test plugin were rebuilt as well, avoiding an
OCaml dynamic-interface mismatch from the compatible optional API additions.

Metadata admission exposes the coefficient-bound proof's actual
unsupported source step `evaluate (+ (to_int 7/2) 1)`; it is not counted as a
proof. Integer tightening and parity may require unsupported Real/to-int
intermediates. The missing generated `arith-geq-tighten` selection belongs to
the coordinator. This child has not substituted a hand-written rule evaluator,
used an unsat bit as evidence, or replaced CPC derivations with a global solver.


The pre-guard-sharing diagnostic of all six LIA benchmark cases has three
proved cases, two 300-second timeouts (disjunctive and inconsistent bounds),
and one unsupported selected rule (strict shift). The timeout results are in
`/tmp/eunoia-lia-live/bench-remaining/results.json` and are not passed counts
or calibrated performance measurements. They overlapped other development
compiles. The coordinator owns the final integrated coverage/timing run.
The smaller nonunit contradiction and negative-bound proofs in the public
suite do pass. Integer tightening, general coefficient-bound implications,
and larger disjunctive benchmark coverage remain incomplete.

An early standalone compile overlapped a default build that changed the
imported SMTCoq artifact fingerprint. Both assumption audit and kernel check
correctly rejected the stale artifact. Final validation therefore runs build,
owned tests, gate replay, compilation, assumption audit and kernel check
sequentially, recording hashes of imported `.vo` and `.cmxs` artifacts before
and after the final proof checks. The exact driver and all commands/exits are
`/tmp/eunoia-lia-suite/final_validation.py` and `final-status.json`.

Integration notes: the coordinator must register `eunoia_lia` in the shared
unit-test module list, update the older adapter-interface description of
binding to mention checked n-ary lowering, and decide the public builder
sigma API. This branch retains `?sigma:Evd.evar_map ref` so newly checked
constraints can be returned to external callers; parent `53e2c32` used an
optional immutable evar map. All existing repository callers build and the
tactic always propagates its actual map into Proofview. No source gate API
or semantic assumption is changed by this API choice.


## Final frozen validation

The composed child at parent merge `40858c2` passed the final sequential run.
Every entry in `/tmp/eunoia-lia-suite/final-status.json` has exit **0**:

1. private-wrapper `dune build -j2`;
2. owned backend/witness `dune runtest -j2`;
3. real typed local-gate replay (75 cases, with mutation rejection);
4. normal `rocq c` on all fifteen public live positive goals and two false
   controls (all positive proofs end in `Qed`, then `Print Assumptions`);
5. recompilation of the exact forall-carrier `Quantified.v` reproduction;
6. baseline assumption audit on 29 declarations;
7. independent recursive `rocq check`, without admission flags, on the live
   module, backend Public/Lia modules, adapter and quantified regression.

The audit passed with no new assumptions:
`/tmp/eunoia-lia-frozen-assumptions/summary.json`. It includes all fifteen
positive public proofs, the false-control theorem, all five arithmetic
replay proofs, the UF integer-carrier and forall-carrier regressions, the
binding/soundness declarations and the exact quantified-carrier reproduction.
The proofs inherit the existing Uint63 specifications and proof irrelevance
where reported; they are not described as assumption-free.

`/tmp/eunoia-lia-suite/changed-artifacts.json` is `[]`: every imported `.vo`
and `.cmxs` hash remained unchanged during this final proof validation.
The repository public source and its compiled standalone copy both hash to
`b651f92e8ca5cc130f231c55f8c723a27bf440afdb0a6679fd3b7694579cf6a7`.
All exact compiler, audit and kernel commands, exits and log paths are in
`final-status.json`; no Dune source registration was substituted for compiling
the actual new public test source.

The fifteen positive goals are actual public `cvc5_eunoia` executions, not
counts of syntax replays or native witness tests. Whole-compiler time was
uncapped for this correctness suite; existing solver, proof expansion,
generation and witness limits were retained. This is not a claim that these
proofs fit the coordinator's 30-second benchmark limit.

The coordinator's separate pinned `1167c11` diagnostic is retained at
`/tmp/smtrocq-lia-milestone-benchmark-status.json` and
`/tmp/smtrocq-lia-milestone-benchmark/runs/cvc5_eunoia/`: five LIA positives
exceeded 30 seconds and strict shift rejected `arith-geq-tighten`; none counts
as passed at that limit. The original six statements remain at
`/tmp/smtrocq-lia-milestone-cases.json`. In particular the exact strict-shift
source and full error are in `lia_strict_shift/1/{case.v,output.log}` under
that run directory. The generator-only owner is handling this source rule.

Later coordinator work is outside the frozen revision: preserve the
`fuel_term` helper and transparent `EunoiaTactic.default_fuel` from `3dd364d`
when integrating this branch, as well as actual-sigma handling. This child
makes no speedup claim for that subsequent representation change. The
performance child owns `eunoiaRocq.ml/.mli`; this child did not modify those
files. The compiler/rule selection remains owned by the generator child.
