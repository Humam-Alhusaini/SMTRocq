# Abstract-carrier UF coverage

This is a bounded witness-search and live-tactic coverage milestone, not overall
CPC backend completion. The suite is `unit-tests/eunoia_uf.v`. Its 22 positive
theorems invoke public `cvc5_eunoia`, using the ordinary production
`Search.produce` and the verified local and final checker gates. Two additional
examples require rejection of false predicate/injectivity goals. There are no
positive goals disguised as expected failures.

The abstract sections use `A : Type`, `HA : CompDec A`, and, where needed,
`B : Type`, `HB : CompDec B`. These are generalized theorem arguments, following
`verit_tactics.v`; no global assumptions are declared. These goals do not use
integer carriers, arithmetic normalization, or a second solver to discharge
local CPC implications.

## Coverage and local witness changes

The positive statements cover symmetry, transitivity and reversed equality
chains; unary, binary and nested congruence; an unchanged function argument;
positive and negative Boolean predicates; equality of Boolean-valued predicate
applications; binary predicates; disequality contradictions; disjunctive roots
and nonunit equality consequences; equality predicates; explicitly supplied
hypotheses; mixed arguments and nested functions across two abstract sorts;
propositional Boolean equality transitivity; and a fully quantified carrier
regression that keeps its proof-local universe rather than using a Section.

Three producer omissions were reproduced and corrected:

* Equality atoms now participate in `EqCgrP` candidate generation. The existing
  `EUF.check_congr_pred` supports `Abop (BO_eq _)`. cvc5's actual proof of
  transitivity uses this operation on an equality predicate; the previous
  producer failed at `@p10 (cong)`.
* Equality paths may use nonunit equality atoms as **conditional hypotheses**.
  Every used edge appears negatively in the emitted `EqTr`/congruence clause;
  resolution must discharge it against the exact roots. The target edge is
  excluded when looking for a transitivity path to avoid hiding useful
  alternatives behind a tautology. Congruence respects an existing target's
  operand order. This handles conditional symmetry and disjunctive equality
  consequences without assuming a disjunct.
* Unit resolution runs first, bounded theory candidates are generated before
  unrestricted propositional saturation, and clause subsumption prunes weaker
  producer work. Before subsumption, the two Boolean equality premises
  `a = b`, `c = d` and conclusion `(a = c) = (b = d)` exhausted 4,096 clause
  slots. The new generic CNF regression passes with the same limits.

The source of a CPC rule is never an input to witness search. These changes
produce untrusted local candidates; the existing gate still recomputes every
operation, checks all ordered root claims and expected outputs, and requires
an empty final clause. No checker semantics or soundness theorem is replaced.
Unused local search commands can be pruned, but no CPC inference is skipped.
Default limits remain 4,096 clause slots, 100,000 resolution pairs, 32 theory
rounds, 128 terms, 256 formulas and 64 arithmetic formula visits.

## Final validation

Branch: `t3/eunoia-uf-witness-coverage`. Worktree:
`/home/charles/.t3/worktrees/SMTRocq/t3-d089e7b0`, initially based on
`dd4694c8c3099653d43b94213066d82d44dcbeab`. Final validation uses coordinator
integration `45b3411`, including source owner `93d11ee` and universe fix
`53e2c32`. All commands below exited 0:

```sh
bash src/eunoia_witness/tests/verify-live-uf.sh
/home/charles/code/friends/.toolchains/smtrocq-env dune runtest --force -j2 src/eunoia_witness/tests
bash src/eunoia_witness/tests/verify-local-gate.sh "$PWD/theories/checker/eunoia/EunoiaLocal.v"
```

Logs, respectively:
`/tmp/smtrocq-uf-complete-suite.log`,
`/tmp/smtrocq-uf-complete-native.log`, and
`/tmp/smtrocq-uf-complete-gate.log`.

The standalone script ran the private wrapper's `dune build -j2 @install`
(exit 0), copied the unchanged test file into
`/tmp/smtrocq-live-uf.rjFR6E/eunoia_uf.v`, and compiled it with the built install
loadpath (exit 0). The full compiler output is
`/tmp/smtrocq-live-uf.rjFR6E/compile.log`, and the install build output is
`/tmp/smtrocq-live-uf.rjFR6E/build.log`. All 22 positive theorems reached `Qed`
and both false-goal controls passed in this single file. No positive case was
removed to make the suite pass.

Every positive theorem has an explicit `Print Assumptions` after its Section
closes. The script additionally audited all 22 exported theorems against
`docs/eunoia/baseline-assumptions.txt`; compiler exit 0, `passed: true`, and
no new assumptions for any theorem. The summary, expanded audit command,
individual assumption reports and compiler log are in
`/tmp/smtrocq-live-uf.rjFR6E/assumptions/`. In particular, the exact result is
`/tmp/smtrocq-live-uf.rjFR6E/assumptions/summary.json`.

The final native/gate suite contains 75 cases: 53 positive candidates and 22
negative/input/budget cases. Every positive candidate is serialized,
typechecked and VM-replayed through the actual Rocq gate. Applicable mutations
also reject bad capacity, missing/reordered roots, altered expected outputs,
changed premises/conclusion, omitted EUF argument evidence, and omitted
Micromega evidence. Shape checking alone is not the acceptance test.

This child grew the original 51 cases to 66 (46 positive, 20 negative/input
cases), preserving every original case. The assigned source owner subsequently
extended that suite to the final 75, including explicit-negation and arithmetic
coverage. The final replay directory is `/tmp/smtrocq-witness-probe.7P6gLN/`.
Its existing gate `Print Assumptions` output is in `gate-assumptions.log`.
The replayed gate SHA256 is
`feb60ebc93dc614ab348fbb3d3c9ccf461b38f958ee6be3751a101b9cb094dcd`.
This child adds no soundness lemmas or global assumptions.

The authored witness commits are `0f2965e`, `3c573a8`, and `49bdcec`. Witness
source was frozen at `49bdcec` for the source owner's handoff. Later witness,
backend, generated runtime, shared tactic and theory changes were integrated
from the coordinator's authorized commits, not edited concurrently here.
All authored changes remain in the assigned witness, new test and new document
paths. No Logos/Ethos checkout, dependency install, network, push or PR was used.

## Registration and reproduction

The coordinator must add `eunoia_uf` to the existing `unit-tests/dune` module
list. This child does not edit that shared stanza. Until registration, run the
standalone script above. It uses the private toolchain wrapper, builds with
`dune -j2 @install`, compiles the unchanged source under a temporary `EunoiaUF`
loadpath, and automatically audits every `Lemma` in the file. All outputs stay
under `/tmp/smtrocq-live-uf.XXXXXX/`.

`bash -n src/eunoia_witness/tests/verify-live-uf.sh` and `git diff --check`
also passed (exit 0). A static audit confirmed 22 direct public-tactic positive
proofs, the same 22 assumption-print commands, exactly two false-goal controls,
and no forbidden declarations or proof holes.

## Resolved cross-layer regressions

These cases exposed actual missing support rather than only testing reflexive
smoke goals. Initial diagnostics are `/tmp/smtrocq-uf-live-initial.log`.
Source proof samples are `/tmp/smtrocq-uf-equality-predicate.cpc` and
`/tmp/smtrocq-uf-equality-transitivity.cpc`. Both were produced by the pinned
private cvc5 1.4.2 binary (commit `282d5e0`), with
`--dump-proofs --proof-format=cpc --proof-granularity=dsl-rewrite
--no-proof-allow-trust --proof-check=eager --check-proofs-complete` (exit 0).

The coordinator's metadata, backend and source jobs corrected `@list` admission,
missing multi-sort instance registration, duplicate supplied/local roots, and
explicit double-negation syntax binding. The initial negative-predicate
failure is `/tmp/smtrocq-live-uf.qbBxXr/compile.log`; its actual CPC proof is
`/tmp/smtrocq-uf-predicate-negative.cpc`. The source fix preserves `Fnot2` at the
CPC boundary and certifies its removal inside local witnesses using the existing
`ImmFlatten` checker. The exact `p x = false` theorem remains in the final suite.

The fully quantified carrier goal originally failed with
`Universe Quantified.23 undefined`, independently reproduced using the built
install loadpath. The failure and precise typechecking backtrace are retained
in `/tmp/smtrocq-uf-quantified-regression/{compile,backtrace}.log`.
The coordinator's `53e2c32` fix passes the actual goal evar map to refutation
typechecking, retaining all VM, type, exact and kernel checks. Its isolated
compile/audit passed in `/tmp/smtrocq-uf-quantified-regression/fixed.log` and
`/tmp/smtrocq-uf-quantified-assumptions/summary.json`. The same fully quantified
statement is also checked in the final 22-theorem file alongside the Sections.

## Remaining limits

Functions consuming Boolean arguments remain unsupported, for example
`forall (f : bool -> bool) a b, a = b -> f a = f b`. The formula representation
uses `Fiff` for the Boolean equality premise; `EUF.get_eq/build_congr` requires
an atomic `BO_eq` premise. No existing proved bridge was found, and this child
does not add an unchecked one. Boolean-valued predicates on abstract carriers
and purely propositional Boolean equalities have separate successful tests.

Search is bounded and incomplete: it can fail on a valid local implication.
This milestone makes no SMT quantifier, BV, array, full CPC signature, LIA
acceptance-suite, or performance comparison claim. Source-generation/backend
failures must be fixed in those layers, never replaced with local rule-name
switches or acceptance of solver answers.
