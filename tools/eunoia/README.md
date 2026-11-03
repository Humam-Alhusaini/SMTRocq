# Eunoia signature compiler: initial fixed-arity subset

This is executable signature compilation, not a rule-name dispatcher. The
Python reader traverses `.eo` includes relative to each including file, records
source hashes, indexes declarations (including CPC forward program declarations
and overloads), and compiles the explicit rule selection and its helper closure
to Rocq data. The generic `EoRuntime` matches and executes that data. Changing a
selected premise, argument, requirement, conclusion, or helper body changes the
generated definition. Rule names have no execution behavior in the runtime.

No SMT interpretation, semantic assumption, solver call, or State update is
introduced. A result is only candidate syntax. See [INTERFACE.md](INTERFACE.md)
for the exact API and the mandatory later checked bridge to existing SMTCoq
semantics/checkers. No overall CPC checker completion is claimed.

Supported constructs:

* Includes, processed once, with missing files and cycles diagnosed; comments,
  SMT-LIB doubled-quote strings, and quoted-symbol lexing.
* Explicitly selected `declare-rule`s with fixed `:args`, fixed ordered
  `:premises`, all `:requires` expression pairs, and `:conclusion`.
* First-order, fully applied constructors; atomic types and polymorphic type
  binders; implicit Type arguments on constructors. Binary `:chainable and`,
  `:left-assoc`, and `:right-assoc` constructors are allowed **only at exactly
  arity two**, where no associative expansion is required.
* Typed `program` signatures and ordered first-order pattern/body cases,
  repeated-variable equality, helper calls (including fuel-bounded recursion).
* `eo::eq` (structural equality), `eo::ite` (Boolean-literal condition),
  `eo::requires` (equality guard), `eo::typeof` (partial query), and exactly one
  non-shadowing local binding in `eo::define`.

All helper arguments/results, rule premises/results, and binder types are
checked with the supplied partial query. Polymorphic type binders are inferred
from matched values, then every binder is checked. An unbound/unused binder or
an unavailable type query rejects execution, rather than supplying a default.
A matching helper case whose body fails cannot fall through to a later case.
Fuel bounds expression traversal as well as recursion; exhaustion returns None.

Unsupported constructs reject compilation if reachable from a selected rule:
`:premise-list`, assumptions/scope, explicit conclusions, `:sorry`/trust,
`:list`/`:opaque` binders, variable-headed or evaluative patterns, overloaded
constructors, partial application, dependent/function/parameterized types,
nil-terminated/argument-list/binder constructors, all unlisted native operations
(including arithmetic and list operations), `define` helpers without explicit
program type signatures, multiple/shadowing local bindings, and quoted/string/
numeric literal terms. The lexer recognizes literals to parse the complete
signature; the initial backend does not interpret them as term data. Unknown
top-level commands, malformed S-expressions, duplicate rule declarations or
fields, conflicting prototypes, and unknown selected names also fail.

An explicit `--rules` selection is mandatory. Unselected rules are listed in
the manifest and absent from the runtime table; this is **not** permission for
a CPC proof reader to skip steps. A proof using any unavailable rule must fail.
This subset cannot execute the complete `/tmp/smtrocq-uf4.cpc`: `evaluate`,
`and_elim`, `cong`, and `trans` are not yet supported. The 13 selected rules and
`$mk_symm` compile from the actual full cvc5 1.4.2 signature; generic equality
requirements, recursion and additional primitives are exercised by regression
signatures. There is currently no selected actual CPC rule with `:requires`.

Reproduce the committed file from the pinned, self-contained source extract:

```sh
python3 tools/eunoia/compile.py tools/eunoia/signatures/Initial.eo \
  --rules refl symm true_intro true_elim false_intro false_elim eq_resolve \
  modus_ponens not_not_elim contra eq-refl eq-symm ite_eq \
  --output /tmp/CpcGenerated.v --manifest /tmp/CpcGenerated.json
cmp theories/checker/eunoia/CpcGenerated.v /tmp/CpcGenerated.v
```

To compile the actual full include tree, replace the first argument with:
`/home/charles/code/friends/.toolchains/cvc5-1.4.2/cvc5-cvc5-1.4.2/proofs/eo/cpc/Cpc.eo`.
For this milestone that reports `13 rules, 1 helpers; 596 rules explicitly
excluded`. Failed parsing/compilation exits 2 before opening either output.
Generated code is deterministic and independent of source paths and selection
order; provenance lives in the separate manifest. The manifest covers sources
and output, not a certification of the Python compiler.

Run all generator tests, byte-for-byte regeneration, kernel computation tests,
and `rocq check` without modifying shared dune files:

```sh
bash tools/eunoia/check-generated.sh
```

The script uses only Python's standard library and the private
`/home/charles/code/friends/.toolchains/smtrocq-env` wrapper. Rocq files compile
in a fresh temporary directory that is deleted afterward. Runtime examples
exercise successes and failures for types, exact premise binding/order/count,
helper cases, recursion, requirements, conditionals, local bindings, unknown
rules, and fuel. These are closed computation proofs, not semantic soundness
lemmas. `Print Assumptions` is run on representative helper/guard examples.

References read before implementation: Logos at
`89df5909b0e9aabb936b68ee95c75a18f609db7a` (`install/install-sig.sh`,
`install/README.md`); Ethos at `f97393ea55f03653689e104d0e9c9010ee17780c`
(`tools/eoc/docs/design.md`, `src/cmd_parser.cpp`,
`src/type_checker.cpp`). Logos invokes Ethos `eoc`; its generated model embeds
SMT semantics independently. This implementation directly compiles a smaller
surface subset and deliberately leaves interpretation to SMTCoq integration.
