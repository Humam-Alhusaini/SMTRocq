# Use SMTRocq

After [installation](INSTALL.md), import the SMTRocq entry point:

```coq
From SMTCoq Require Import SMTRocq.
From Stdlib Require Import ZArith.
Local Open Scope Z_scope.

Goal forall (f : Z -> Z) (x y : Z), x = y -> f x = f y.
Proof. smtrocq. Qed.

Goal forall x y : Z, x <= y -> y < x + 1 -> x = y.
Proof. smtrocq. Qed.
```

The inherited SMTCoq tactics, including `verit`, remain available. Their original
usage guide is preserved [here](docs/upstream/USE.md).

The optional `cvc5_eunoia` tactic also checks CPC source conformance through the
separate checker dependency. See [the two checking contracts](docs/architecture.md#two-checking-contracts).

Array goals additionally import `SMTCoq.structures.FArray`:

```coq
From SMTCoq.structures Require Import FArray.

Goal forall (a : FArray.farray Z Z) (i j v : Z),
  i <> j -> FArray.select (FArray.store a i v) j = FArray.select a j.
Proof. smtrocq. Qed.

Goal forall x y : Z, Z.abs (x+y) <= Z.abs x + Z.abs y.
Proof. smtrocq. Qed.
```

See [the theory coverage guide](docs/theory-coverage.md) for supported
combinations and remaining limitations.

Bitwise goals use SMTCoq's existing bit-vector type:

```coq
From SMTCoq.structures Require Import BVList.
From Stdlib Require Import NArith.
Import BITVECTOR_LIST.

Goal forall x y : bitvector 8%N,
  bv_not (bv_and x y) = bv_or (bv_not x) (bv_not y).
Proof. smtrocq. Qed.
```

The current semantic producer supports concrete positive widths up to 64
for bitwise operations, constants, equality, concatenation, extraction, and
zero/sign extension. See the coverage guide
for operations still needing certificate production.

For example, reconstruct a 64-bit word from its two halves:

```coq
Local Open Scope N_scope.
Goal forall x : bitvector 64,
  bv_concat (@bv_extr 32 32 64 x) (@bv_extr 0 32 64 x) = x.
Proof. smtrocq. Qed.
```

Extraction ranges must be within the source word. These examples use the
`BITVECTOR_LIST` import from the preceding example.
