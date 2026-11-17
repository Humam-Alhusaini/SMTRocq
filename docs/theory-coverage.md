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
| Fixed-size bit vectors | SMTCoq has bit-vector semantics and a small checker. Add native CPC-to-bit-blasting certificate production and end-to-end tests before claiming CVC5 support. |
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
