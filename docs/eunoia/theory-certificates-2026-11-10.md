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
experiment, which still executes a local command program. The new feature's
performance and default-selection decision are recorded after the matched run.
No speedup or veriT parity is inferred from certificate coverage alone.

The proof and mutation tests are in `EunoiaTheoryTests.v`. They cover successful
and incorrect equality/congruence/arithmetic certificates, false-clause fallback,
changed arithmetic coefficients and premises, invalid bounds, exact ordered
cache references, unused invalid entries, and invalid source or semantic steps
after a conflict. No axioms or admitted proofs are introduced; SMTCoq's inherited
UInt63 and proof-irrelevance assumptions remain part of the documented baseline.
