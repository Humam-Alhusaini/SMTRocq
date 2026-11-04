# Rocq integer division facts

`cvc5_eunoia` adds proved facts for occurrences of Rocq's `Z.div` and
`Z.modulo` with ground integer divisors. The existing SMTCoq reifier exports
these functions as UF symbols; the checker still uses its existing UF/LIA
semantics. This does not introduce an SMT-LIB division interpretation.

The facts come from [EunoiaDivision.v](../../theories/checker/eunoia/EunoiaDivision.v),
using the standard library's verified integer division lemmas. Positive and
negative divisors get reconstruction and the appropriate signed remainder
bounds. Zero uses Rocq's actual convention: `x/0 = 0` and `x mod 0 = x`.
This distinction matters when comparing with solvers' totalized division.

The collector also supplies periodicity and quotient-shift identities for
`x + k` and `x - k` when the ground offset is divisible by the nonzero divisor.
Nested quotients normalize when the inner divisor is a nonzero constant and
the outer divisor is a positive constant. The positive outer-divisor restriction
is required by Rocq's floor division; the analogous negative case is false.
Constants are normalized as Rocq integers, without conversion to OCaml integers.

Every fact is an actual proof term. It is reified and bound to the complete
ordered source-root vector alongside user hypotheses. The final proof applies
these terms, and the kernel checks the certificate helpers and resulting
proof. Neither the solver nor the collector can declare a fact true.
All generated CPC computations, bindings and local semantic gates still run,
including for unused steps after a conflict.

Fact collection is deduplicated, capped at 64 facts and a 100,000-node traversal.
Binders and branches are skipped to avoid exporting bound variables from their
scope. The public preprocessor introduces outer quantifiers first. Variable
divisors, arbitrary nonlinear multiplication and general recursive division
normalization are outside this extension. Hitting a collection bound may leave
a goal unsolved; it does not relax checking.

[Public regressions](../../unit-tests/eunoia_division.v) cover signed and zero
constants, large integers, hypotheses, UF composition, shifts and nested
quotients, including false controls. The separate
[division manifest](../../benchmarks/eunoia/division.json) keeps these results
apart from the original UF/LIA benchmark. A baseline backend is measured with
its normal tactic behavior, without Eunoia's added theory facts; report that
scope difference when comparing results.
