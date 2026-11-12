# Array and integer-operation coverage

The `smtrocq` semantic tactic now includes array read/write and extensional
reasoning, and proved facts for common Rocq integer operations. Use the public
`SMTRocq` entry point; array goals additionally import `SMTCoq.structures.FArray`.

```coq
From SMTCoq Require Import SMTRocq.
From SMTCoq.structures Require Import FArray.
From Stdlib Require Import ZArith.
Local Open Scope Z_scope.

Goal forall (a : FArray.farray Z Z) (i j v : Z),
  i <> j ->
  FArray.select (FArray.store a i v) j = FArray.select a j.
Proof. smtrocq. Qed.

Goal forall x y : Z, Z.abs (x+y) <= Z.abs x + Z.abs y.
Proof. smtrocq. Qed.
```

## Coverage and checking boundary

The public array suite covers reading at the written index, reading elsewhere,
overwriting, storing the current value, commuting distinct writes, aliases,
arithmetic index equalities/disequalities, integer value bounds, UF over reads,
and reading an array stored inside another array. These are actual Rocq
`FArray` values with SMTCoq's existing comparison/default-value semantics.

`ArrayCommand` checks read-same, read-other, and extensionality using the existing
verified SMTCoq array small checkers. It checks fresh bounded destinations,
all input literal bounds, exact canonical output, and rejects the checkers'
default-true failure result. Read-other retains its required input order;
only its computed output is sorted, with a correctness proof. No array
semantics or SMT axioms are implemented afresh.

Native array production closes nested read dependencies before saturation.
Extensionality witnesses belong to actual root equalities; generated congruence
equalities do not spawn an unbounded tower of difference witnesses. When
saturation is insufficient, bounded splitting on reachable read/write index
equalities reconstructs a single ordinary resolution certificate. Temporary
branch assumptions never become submitted roots. Both reconstructed clauses
and every retained operation pass the same verified local gate.

The producer uses at most three split levels and fifteen searches. Each search
has 512 clause slots, 4,096 resolution pairs, six theory rounds, 256 terms,
1,024 formulas, and 64 arithmetic literal visits. The combined certificate is
bounded by 4,096 slots. Failure retains the existing translation path and can
still result in an unsupported-goal error. These limits bound untrusted search;
they do not bypass any checker test.

The integer suite covers absolute value, minimum, maximum, sign, signed modulo
bounds for symbolic divisors, zero division/remainder, and substitution of a
proved ground divisor, including reversed equalities and mixed UF. Nine new
lemmas prove facts about the actual standard-library functions. The existing
bounded fact collector instantiates them only for operations in the actual
goal/hypotheses; a known-divisor substitution takes the actual equality proof.
Facts are deduplicated and capped at 64, with the existing 100,000-visit limit
and exclusion of binder/branch-local variables.

Whole-arithmetic compression retains its small-input behavior and accepts up to
24 atom occurrences under the existing 64-node limit. For more than twelve
atoms it additionally bounds the Boolean case expansion by 128 before invoking
Micromega. This avoids large CPC fallback traces for combinations of proved
operation facts. The complete certificate and original root vector remain
checked.

Array production runs only on array goals. Ordinary UF/LIA retain their
existing compact producers. `cvc5_eunoia` still additionally checks the original
signature-generated CPC derivation; this extension does not claim broader CPC
array-rule conformance. The fast `smtrocq` tactic proves the actual theorem with
semantic certificates, as documented in the
[original checking contract](smtrocq-tactic-2026-11-11.md).

## Limits

This is useful combined UF/LIA/array coverage, not all SMT-LIB theories. Search
is bounded. End-to-end array coverage is tested for integer keys and integer or
nested-array elements; Boolean/abstract array configurations are not claimed
here. Unrestricted symbolic integer division reconstruction introduces
nonlinear products and is outside this linear arithmetic extension. General
nonlinear arithmetic, reals, bit vectors, strings, datatypes, and unrestricted
quantifier instantiation remain outside this checkpoint's supported scope.

## Reproduce

The new public suites contain 42 positive cases and seventeen false-goal
controls. `EunoiaArrayTests` supplies fixed solver-free array certificates and
corruption controls. Native tests additionally exercise branch reconstruction,
Boolean goal wrappers, corrupted arguments, out-of-bounds arguments, and invalid
array commands after conflict.

```sh
python3 -B benchmarks/eunoia/run.py --skip-build --entrypoint SMTRocq \
  --cases benchmarks/eunoia/arrays.json --extra-import SMTCoq.structures.FArray \
  --backends verit smtrocq --repeat 2 --timeout 30 --output /tmp/array-comparison
python3 -B benchmarks/eunoia/run.py --skip-build --entrypoint SMTRocq \
  --cases benchmarks/eunoia/integer-operations.json --backends smtrocq \
  --repeat 2 --timeout 30 --output /tmp/integer-operations
```

The standalone checker includes byte-identical array gates, integer lemmas,
and fixed array fixtures, but no native producer or public tactic. Its array
benchmark layers explicitly measure semantic certificates separately from
strict CPC source validation.
