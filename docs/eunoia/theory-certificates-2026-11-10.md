# Direct SMTCoq theory certificates

The Eunoia semantic backend now supports compact certificates that call SMTCoq's
verified theory checkers directly. `EunoiaTheory` proves their soundness. Its
untrusted OCaml producer selects operations from actual formulas and clauses,
without CPC rule names. Generated CPC source validation remains mandatory.

The initial operations are truth, exact premise reuse, equality transitivity
(including reflexivity and symmetry), congruence, and Micromega arithmetic.
For unit-premise theory steps the checker constructs the conditional clause,
checks it with `EUF.check_trans`, `EUF.check_congr`, or `LIA.check_micromega`, and
proves that actual premise validity implies conclusion validity. This avoids
allocating a local clause machine, loading the negated conclusion, and resolving
to a fresh conflict for every supported source step. Nonunit arithmetic premises
and other unsupported shapes retain the existing verified local certificates.

Equality and congruence candidates are produced directly. Atomic arithmetic
implications request a Micromega certificate directly on the exact sorted
conditional clause, with a bounded formula count. Pure UF equalities avoid
arithmetic search. Other arithmetic cases can reuse a matching Micromega proof
from the existing producer; Boolean expansion and mixed-theory discovery retain
the bounded fallback.

`EunoiaMemo` supports both local-program and theory cache entries. Every cache
entry is checked, including unused ones; each reference still compares actual
ordered premises and conclusion. Bounds checks, exact root/source bindings,
scope discharge, fresh writes, and validation after a conflict remain in force.
The default-true fallback of the theory checkers is rejected. Explicit truth
has its own certificate requiring the actual true clause.

Set `EUNOIA_THEORY_CERTIFICATES=1` to select the new producer, or `=0` for the
reference producer. This differs from the older `EUNOIA_DIRECT_CERTIFICATES`
experiment, which still executes a local command program. The new feature remains opt-in: the matched comparison below did not establish
a robust overall speedup. No speedup or veriT parity is inferred from certificate
coverage alone.

The proof and mutation tests are in `EunoiaTheoryTests.v`. They cover successful
and incorrect equality/congruence/arithmetic certificates, false-clause fallback,
changed arithmetic coefficients and premises, invalid bounds, exact ordered
cache references, unused invalid entries, and invalid source or semantic steps
after a conflict. No axioms or admitted proofs are introduced; SMTCoq's inherited
UInt63 and proof-irrelevance assumptions remain part of the documented baseline.

## Frozen full-tactic comparison

Core `910425da6e2f8ba059ed217c26cb9491fb3fb3ba` was built once, including
the producer's own native library. A reference/direct/direct/reference sequence
then changed only `EUNOIA_THEORY_CERTIFICATES=0/1`. Both paths used the default
direct Boolean frontend, printed conclusions, automatic indexed encoding, and
adaptive checked sharing; other experimental modes stayed off. All checker
source and installed proof/native-library fingerprints remained identical.
Each fresh compiler had a 30-second deadline; independent audits used 900 seconds.
An earlier incomplete run invalidated by a concurrent fixture edit was discarded.

The standard suite passed all 144 positive attempts and 16 false-goal rejection
attempts. The focused run passed 32 positive attempts with assumption auditing,
and four false-goal/source/semantic corruption groups. The table sums per-case
medians of tactic plus `Qed`; compiler startup is recorded separately.

| Standard workload | Reference | Direct theory certificates |
| --- | ---: | ---: |
| UF | 5.002 s | 6.127 s |
| LIA | 4.829 s | 5.119 s |
| Total | 9.831 s | 11.246 s |
| Corresponding veriT control total | 2.729 s | 3.122 s |

The raw direct total is 14.4% slower, while the corresponding veriT controls
also slow by 14.4%. The runs therefore do not establish an overall performance
effect. Individual diagnostics are mixed: nested UF at depth 40 changes from
1.493 s to 1.587 s, and disjunctive LIA from 1.309 s to 1.362 s. The 64-link
chain's reference measurements vary from 5.100 s to 11.450 s; its aggregated
improvement is not a reliable speedup claim. The direct variant still trails
its corresponding veriT standard controls by about 3.60 times overall.

For these reasons the new path is available for development and standalone
measurement, with the production default retaining the reference producer.
Direct primitives eliminate local machine construction for their supported
steps, but the full generated source evaluator and the Rocq VM compilation,
conversion and proof-acceptance costs remain. This implements the compact
verified semantic layer of the SMTCoq approach; it does not complete the
performance goal or replace every local certificate.

[All rows, controls, sources and artifact fingerprints](theory-certificates-measurements-2026-11-10.json)
retain the complete comparison, including unfavorable results. To reproduce the
standard comparison, run `benchmarks/eunoia/run.py --skip-build --backends verit
cvc5_eunoia --repeat 1 --timeout 30 --output <new-directory>` four times with
flag values `0,1,1,0`, after building `@install` and all native libraries. Do not
edit checker inputs or run other compilation/checking jobs during measurement.

## Final verification

The complete install/regression build passed, including 98 native witness cases.
Twenty-two selected compact candidates were additionally serialized, typechecked
and recomputed by the actual Rocq theory gate. All 37 new proof and mutation
examples passed. The expanded 428-target assumption audit and independent
recursive kernel replay passed against the unchanged inherited baseline.

Eighteen fresh integration/public replay modules passed across direct, forced
sharing, inline, and indexed-source modes, with separate recursive kernel checks
for each replay group. The direct path is included in the default CI checks,
while the production producer remains opt-in. The standalone extraction matches
all 133 proof/signature files at the core checkpoint and passes its full build,
238-target audit and six fresh component/kernel replays.

[Exact final verification, source hashes and commands](theory-certificates-validation-2026-11-10.json).
