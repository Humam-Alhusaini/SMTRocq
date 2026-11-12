# Integer cuts with rational proof intermediates

The object theory remains SMTCoq's existing integer theory. CVC5 sometimes uses
`to_real`, `to_int` and rational constants while proving integer parity or rounded
bounds. `EunoiaIntegerEmbedding.v` lowers these restricted intermediates to integer
syntax without adding a Real interpretation or changing the raw CPC proof.

A fractional expression carries an integer numerator and a strictly positive
`positive` denominator. Comparisons use exact cross multiplication; equal
denominators avoid redundant coefficients. Addition, multiplication, negation,
comparison and integral-floor identities have Rocq proofs. A floor with a
non-unit denominator requires a closed expression and uses exact rational floor,
including negative values. Division requires a closed nonzero divisor. Free Real
variables and non-ground fractional floors fail explicitly.

The adapter's fixed metadata query checks cast arities and input sorts. Object
encoding still rejects Real sorts. The native producer calls the same Rocq
normalizer before using the existing integer reifier. The checker independently
binds each normalized conclusion to its authoritative Atom/Form tables. Every
raw source step still passes the signature-generated computation and a semantic
CNF/EUF/LIA certificate check; normalization does not authorize an inference.
The original integer goal roots and final contradiction retain their existing
checked binding. No source step is removed, including unused steps.

`unit-tests/eunoia_integer_casts.v` contains 12 public proofs: signed parity,
two-variable parity, positive/negative coefficient bounds, scoped Boolean and
propositional bounds, and a mixed UF/integer cut. Five false-goal controls check
over-strong bounds and satisfiable equalities. The domain suite additionally
checks wrong sorts/arities, changed denominators, floor versus truncation,
zero division, non-ground floor rejection, zero fuel and reserved-name shadowing.
Both native certificate modes replay the live suite and undergo independent
kernel checks. The assumption audit compares dependencies with the inherited
SMTCoq baseline; this adds no axioms or admitted proofs.

The additional `arith_trichotomy` rule is generated from the pinned CPC
signature. Its helper closure brings the selected signature to 85 rules and
57 helpers. The source declarations and solver pin are unchanged.

For reproducible solver experiments, `EUNOIA_CVC5_PROFILE=reduced` selects a
fixed simplification-disabled option list; `default` preserves the standard
profile. Unknown profile names are rejected. Both profiles retain eager,
complete, trust-free solver proof production and the same Rocq checking path.
The reduced profile did not fix the equality-chain timeout and is not the default.
