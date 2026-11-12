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
