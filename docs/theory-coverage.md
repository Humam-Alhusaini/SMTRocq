# Native SMT-LIB theory coverage

SMTRocq builds on SMTCoq. The fast `smtrocq` tactic checks semantic
certificates for the actual Rocq goal. It does not certify every original
CPC instruction; `cvc5_eunoia` has that additional checking contract.

## Current extension

The array backend reuses SMTCoq's `FArray` semantics and verified array
small checkers. Certificates cover read-after-write at equal and distinct
indices and array extensionality. The native producer combines these with
Boolean resolution, congruence, and integer arithmetic. It can split on
reachable index equalities and reconstruct resolution proofs; temporary
search assumptions are not submitted as roots. Search remains bounded. End-to-end coverage currently uses integer keys and
integer or nested-array values. A Boolean-valued read-after-write probe
still fails local witness production; Boolean array support is not claimed.

The integer fact collector supplies proved laws for `Z.abs`, `Z.min`,
`Z.max`, `Z.sgn`, symbolic signed remainder bounds, division by zero,
and substitution of a divisor known equal to a numeral. These are facts
about Rocq's functions, not unverified SMT-LIB axioms. In particular,
Rocq's zero-divisor behavior and signed remainder convention must not
be confused with a solver's underspecified operations.

Public regressions: `unit-tests/smtrocq_arrays.v`,
`unit-tests/smtrocq_integer_operations.v`, and
`unit-tests/smtrocq_theory_combinations.v`.
Checker proofs and solver-free corruption controls remain in the pinned
`external/rocq-eunoia-checker` dependency.

## Remaining theory work

| Theory family | Status and next implementation boundary |
|---|---|
| Core Boolean reasoning, UF | Existing certificate path; continue combined-theory regressions. |
| Linear integer arithmetic | Existing certificate path plus proved operation facts. General symbolic division and nonlinear multiplication remain incomplete. |
| Arrays | Read/write/extensionality certificates; expand tested key/value sorts and scaling workloads. |
| Fixed-size bit vectors | Semantic certificates for bitwise AND/OR/XOR, NOT, constants, and equality at concrete widths up to 32. Arithmetic, comparisons, extraction, concatenation, extensions, and shifts still need producer support. |
| Reals and mixed integer/real arithmetic | Need Rocq reification, solver encoding, and verified arithmetic certificates. Existing rational CPC intermediates do not establish native real-goal support. |
| Nonlinear integer/real arithmetic | Need dedicated verified certificates. A sound tactic must retain failure/unknown outcomes. |
| Datatypes | Need Rocq constructor/discriminator/selector semantics and verified certificates, including recursive cases. |
| Strings, sequences, regular languages | Need explicit Rocq semantic representations and verified word/length/regular-language evidence. |
| Floating point | Need exact IEEE semantics, rounding modes, and verified reduction/certificates, potentially through bit vectors. |
| Sets, bags, other solver extensions | Determine standardized versus solver-specific semantics, then provide verified reductions or dedicated checkers. |
| Quantified formulas | Need checked instantiation and binder handling; theory coverage alone does not supply quantified completeness. |

Each new theory must cross the complete boundary: Rocq semantics and
reification, SMT-LIB export, untrusted evidence production, verified
certificate acceptance, and connection back to the original theorem.
A parser accepting an operator is not theory support. Existing UF/LIA
performance and false-goal rejection remain release checks.

Supporting all theory families does not mean deciding every formula.
Unrestricted integer arithmetic and quantification prevent that guarantee.

## Validation checkpoint: November 17, 2026

The integration on `feature/theory-coverage` passed a clean `@install` build,
full `@runtest`, and fresh-process replay of all three extension suites.
The public extension has 46 positive goals and 18 false-goal controls;
the native witness suite has 110 cases. The 545-target assumption audit
found no additions to the inherited baseline, and independent recursive
kernel validation passed. This does not remove SMTCoq's existing UInt63
and proof-irrelevance assumptions.

Three serial rounds of the standard 18-case UF/LIA workload solved every
positive goal and rejected both false-goal controls for every backend/run.
The sum of per-case median tactic-plus-`Qed` times was 1.178 s for merged
main's implementation, 1.228 s for this extension, and 2.161 s for veriT.
The extension was 4.2% slower than the baseline and 43.2% faster than veriT
at that boundary. Summed per-case median whole-compiler times were
42.834 s, 44.513 s, and 42.996 s respectively: the extension was 3.5%
slower than veriT for complete compiler processes. These are small-workload
measurements on this environment, not universal speed claims.

[Machine-readable validation](theory-validation-2026-11-17.json) records
case medians, implementation/checker revisions, audit counts, and evidence
hashes. Full commands and artifacts remain at the recorded workspace paths.
Reproduce the proof audit with `python3 -B scripts/eunoia/check_proofs.py`
after building; benchmark commands are in `benchmarks/eunoia/README.md`.

## Bit-vector certificate path

The `feature/bitvectors` extension uses the existing `BVList.BITVECTOR_LIST`
semantics and BVA small checker. The local gate admits exactly `BBVar`,
`BBConst`, `BBNot`, `BBOp`, and `BBEq`, with all premise slots enumerated.
The existing guards require available premises, fresh bounded destinations,
bounded literals, exact outputs, and rejection of default-true failure results.
No new bit-vector semantics or axioms are introduced.

The untrusted producer builds per-term bit lists and uses Boolean CNF and
resolution certificates to discharge the resulting problem. Per-bit equality
conjunctions retain their original bit order. Bitwise expression sharing may
canonicalize commutative operands; the BVA checker independently verifies them.
Rocq's `zeros` constructor is reified as a concrete zero bit vector and remains
bound to the original goal by checked conversion.

This path supports concrete positive widths up to 32. Production is bounded
by 256 terms, 4,096 formulas, 8,192 clause slots, 100,000 resolution pairs,
and four saturation rounds. These are search bounds, not completeness claims.
Theory detection memoizes the actual term/formula DAG; it does not expand
shared UF terms into trees.

The public suite is `unit-tests/smtrocq_bitvectors.v`; solver-free fixtures
and corruption controls are in the standalone dependency's
`EunoiaBitvectorTests.v` and native gate replay. The standalone checker still
owns the verified acceptance layer. This extension certifies semantic proofs
with `smtrocq`; it does not establish CPC bit-vector rule conformance for
`cvc5_eunoia`.
