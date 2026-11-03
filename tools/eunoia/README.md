# Signature-generated CPC computation

This compiler emits executable **syntax computation**, not SMT semantics or
semantic proof evidence. `derive` must be followed by the exact table adapter
and a verified semantic gate for every trace step. No whole port completion is
claimed.

The vendored cvc5 1.4.2 signature is the complete 35-file include closure;
`cpc-manifest.json` records every source hash and transitive helper dependency.
The generated subset currently has **49 rules and 53 programs**, covering the
**98 actual steps in all seven repository UF fixtures**, plus
**411 steps in eight LIA fixtures** (including 12 scope pops). In particular all
15 `unit-tests/eunoia-fixtures/default/uf4.cpc` steps compute in Rocq. The tests
include unused steps; they do not merely check isolated hand-written rule
instances. Actual solver proof bytes and source-input hashes are retained in
`tests/fixtures/`, with commands/exit codes in `provenance.json`.

Regenerate or validate locally:

```sh
python3 tools/eunoia/regenerate.py
EUNOIA_KEEP_TEST_DIR=1 tools/eunoia/check-generated.sh
```

The latter runs Python compiler/decoder tests, compares regenerated code **and**
manifest byte-for-byte, compiles the runtime, source-mutated signatures and
actual fixture replays with the private Rocq wrapper, then independently runs
`rocq check`. It changes no dune, core, adapter or tactic files and installs no
dependencies. Without `EUNOIA_KEEP_TEST_DIR=1` it removes its temporary directory.

For other explicit subsets:

```sh
python3 tools/eunoia/compile.py tools/eunoia/signatures/cpc/Cpc.eo \
  --rules refl symm trans cong and_elim evaluate eq-refl eq_resolve \
  --output /tmp/CpcSubset.v --manifest /tmp/CpcSubset.json
```

Selection is compilation input, never a rule-name implementation switch.
Declarations and helper bodies come from `.eo`, including recursive ordered
cases, repeated-variable matching, requirements and helper definitions. Unknown
rules and unsupported declarations/operations fail closed. The public API and
surface representation contract are in [INTERFACE.md](INTERFACE.md).

Supported syntax computation includes closed and type-dependent nil variadic operators, premise
lists, list-tail patterns, curried/variable-headed applications, lexical
capture-free definitions/parallel lets, lazy conditionals, failure-aware guards,
Boolean literal operations and generic ordered/multiset list operations.
Programs match their source patterns without imposing additional runtime type
annotation constraints; rule binder checks and explicit `eo::typeof` still use
an untrusted query. The production default uses `EoArithmetic.eval` and a deterministic syntax
ordering. `derive_with no_extension` remains available for explicit fail-closed
primitive isolation.

The 560 excluded rules are listed exactly in the manifest. The manifest also
lists six unavailable primitives reached in preserved, unexecuted helper
branches: string/BV conversion, length, concatenation, extraction and find.
Reaching them returns a missing-primitive diagnostic; no source cases are
pruned. Broader attributed operator elaboration and mixed Real/Int semantic
checking remain incomplete. The
initial extracted `signatures/Initial.eo` remains as historical test data;
it is no longer the production generation source.

See [LIA-VALIDATION.md](LIA-VALIDATION.md) for source pins, the ordering invariant,
query examples, scoped computation harness, negative tests and integration limits.
The minimal `arith-geq-tighten` extension, actual 32-step strict-shift proof,
mutation checks and compatible semantic-integration handoff are recorded in
[STRICT-SHIFT-VALIDATION.md](STRICT-SHIFT-VALIDATION.md). Across both original
and reduced captures, all 994 steps in 29 proofs are computed; this does not
establish live semantic acceptance of those proofs.
