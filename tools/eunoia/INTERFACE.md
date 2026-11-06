# Signature compiler / checked-core boundary

`EoSyntax.term` and the public entry point are unchanged:

```
Symbol : string -> term
Apply : term -> term -> term
CpcGenerated.derive : nat -> (term -> option term) ->
  string -> list term -> list term -> option term
```

These are CPC surface terms, with curried application and omitted implicit
arguments. The arguments to `derive` are fuel, partial type query, rule name,
explicit arguments, and exact ordered premise formulas. `Some t` is a syntactic
candidate only. Every step, including an unused one, must additionally pass the
coordinator's exact premise/result binding and verified semantic gate. No
solver result, signature computation, or type query is semantic evidence.

## Surface agreement with the adapter

Read against the authoritative adapter interface and `EunoiaAdapter.v` at
`85a5694d784632c1186783241a84656cfa252c41` / `af4979649dbf48f2eb4294a39f69700aee227b89`.
The generator consumes and returns flat, left-curried `(and p q r)` / `(or p q)`
syntax. It does not expose its internal nil-terminated representation to the
adapter. Internally it elaborates each *surface argument position* into a cons
spine using the signature's closed `:right-assoc-nil` attribute; nested Boolean
operators remain nested elements. After computation it decodes these spines
back to flat applications, preserving order, multiplicity, and nesting. No
associative flattening, duplicate removal, or Boolean simplification occurs
unless the selected source program explicitly requests it.

An internal empty list decodes to its declared nil (`true` / `false`); an
internal singleton decodes to `(and p)` / `(or p)`, not `p`. A source
`eo::list_singleton_elim` explicitly performs singleton elimination. The adapter
currently rejects singleton formula operator nodes, so those results need
separate integration work; this generator does not silently repair them.
Internal list aliases such as `@list`, `@list.nil`, and `@List` are expanded using
source definitions and restored by generated alias metadata. Signed numeral
symbols remain exact (`-2` is distinct from `(- 2)`).

Binary surface `:chainable`, `:left-assoc`, and `:right-assoc` applications are
supported. Larger arities and unsupported attributes/dependent nils fail before
case selection, preventing accidental selection of a helper's fallback branch.
The generated manifest enumerates these excluded attributed constructors.

## Type query and helper execution

Rule binders are inferred from matched values and checked through the query;
premises and results must query as `Bool`. Missing information rejects.
`eo::typeof` invokes that same query after converting internal syntax to surface
syntax. Queries return CPC types, with `Bool` / `Int` / named sorts having type `Type`.
The merged adapter returns flat first-order arrows, e.g. `(-> U U Bool)`.
Those work unchanged for the selected rules: their value binder types are
sorts, and programs traverse partial applications syntactically. Function-type
patterns in retained program annotations are curried metadata; general dynamic
unification of flat arrows against function-typed rule binders is not claimed.
The actual adapter's query remains responsible for supported table-derived
syntax and types. It is executable input, never an assumption in a soundness
lemma.

Program cases match syntax in source order with repeated-variable equality.
Once a case matches, a failing guard/body returns failure without trying later
cases. Program binder/signature annotations remain generated metadata; they
are not additional runtime pattern constraints. This follows Ethos
`evaluateProgramInternal` at `f97393ea55f03653689e104d0e9c9010ee17780c` and Logos
at `89df5909b0e9aabb936b68ee95c75a18f609db7a`. The previous fragment's extra helper
input/output/binder type checks incorrectly rejected legal traversals of bare
polymorphic `=` during `cong`. Rule binder checks and explicit `eo::typeof`
remain. `define` / `eo::define` expand lexically without capture; let bindings
are parallel substitutions, with unused values/unselected branches unforced.

`rule` adds `rule_premise_list : option string`. A premise-list is gathered in
exact input order, preserving duplicates. `expression` adds `ENative`, `EIsOk`, and `EIsEq`; no term
constructors changed. `run_rule` remains available for plain tables, while
generated `derive` uses `run_surface_rule_with` plus generated operator and alias
metadata. No rule-name dispatch occurs in the interpreter.

## Generic primitive extension hook

```
EoRuntime.primitive_hook := string -> list term -> option term
CpcGenerated.derive_with : primitive_hook -> nat ->
  (term -> option term) -> string -> list term -> list term -> option term
```

`derive = derive_with default_primitive`; the default dispatches literal
operations to `EoArithmetic.eval` and `eo::cmp` to `EoOrder.eval`. The hook implements generic EO literal
operations, not CPC rules. It receives evaluated **internal** syntax arguments
and returns internal syntax or `None`. Native Booleans, literal predicates and
operator-aware list operations are supplied by the runtime. Unimplemented bit-vector, string and datatype primitives fail closed.
The manifest records all referenced native operations; full helper bodies and
all source includes are retained even for branches that reach an unavailable
primitive. An arithmetic extension should implement exact signed/rational
literal arithmetic here, leaving relation tables, polynomial algorithms and
rule guards generated from `.eo`. Dependent nil elaboration uses source-generated `cpc_nils`, `ENil` and `PNil`.
`resolve_nil` matches the constructor element or tail domain type against a queried operand type,
binds its implicit parameters, then evaluates the signature's nil body. Closed
nil operators use `cpc_operators`. Neither mechanism changes public `Symbol` or
`Apply` terms.

## Build ownership

No core, adapter, semantic bridge, tactic, or dune file is changed. The existing
public `derive` API lets the coordinator use the merged adapter unchanged.
`tools/eunoia/check-generated.sh` compiles isolated copies, regenerates from the
vendored byte-identical cvc5 signature, replays all actual UF fixture steps,
and independently kernel-rechecks the tests. Semantic certificate coverage,
reader/tactic wiring, and full port completion remain coordinator-owned work.

## Assumption-bearing rules (scope adapter dependency)

```
CpcGenerated.derive_assuming : nat -> (term -> option term) ->
  string -> term -> list term -> list term -> option term
```

Arguments are fuel, type query, rule name, **actual pushed formula**, explicit
arguments, and the exact ordered local premise formulas. The rule IR adds
`rule_assumption : option pattern`, generated from `:assumption` in the source.
Matching that pattern seeds the same environment used for argument/premise
matching and requirements. The pushed formula must query as `Bool`; its exact
surface tree is matched without Boolean normalization. There is no scope-name
special case. A novel rule with assumption `(not F)` is tested as well as the
real source rule.

Ordinary `derive` / `derive_with` pass no assumption and reject any
assumption-bearing rule. `derive_assuming` rejects ordinary rules, unknown
rules, mismatched assumption patterns, non-Boolean pushed terms, mismatched or
extra/missing premises, and failed guards. `derive_assuming_with` additionally
takes the generic primitive hook as its first argument. The shared internal
`derive_context_with` accepts an `option term` assumption. Existing ordinary
public APIs and term constructors are unchanged.

The selected source rule `scope` computes `(=> F G)` from the actual matched
pushed `F` and exact local premise `G`. The selected source `process_scope`
remains an ordinary rule; its source helpers collect nested antecedents and
produce the same flat Boolean surface syntax as the adapter. These are only
computations. The coordinator's `scope_eval : payload -> pushed_literal ->
exact_local_clause -> option clause` must faithfully encode both supplied
arguments from the checked tables, call `derive_assuming`, bind the result,
and use the proved conditional invariant/discharge in `EunoiaScope`. Neither
entry point proves a local premise unconditionally or authorizes a State write.


## LIA computation additions

`evaluate_computation` exposes `Done term`, `Stuck`, and `Missing reason`.
An available arithmetic conversion of a variable is stuck; EO predicates can
observe that result as specified by Ethos. A missing implementation or type
query propagates through `is_ok`, `is_eq`, and literal predicates. Custom hooks
should answer `eo::supports [Symbol native_name]` with `true` only for operations
they implement. A successful result from an old hook still works without the
capability response; `None` from such a hook is treated as missing.

`collect_application_hints` derives function-variable types from exact matched
application contexts using the supplied argument/result type query. Hints are
indexed by source binder ID and must agree at repeated occurrences and with
any explicit query result. They never assign an arbitrary integer type to bare
polymorphic equality. Program annotations remain metadata as before; this
contextual check applies to rule binders.

`cpc_signature_names : list string` contains every constant, parameterized
constant, alias/macro name in the entire pinned include closure, plus native
`Type`, `Bool`, Boolean values, arrow and meta-list constructors. It excludes
rule names, program names, local binders and extension hooks. It includes
unselected/unsupported constants so a reader can prevent lexical shadowing;
namespace membership is not semantic support or step acceptance.

Required surface query examples and build integration details appear in
[LIA-VALIDATION.md](LIA-VALIDATION.md). No shared dune file is modified here;
retain the parent's `tools/eunoia/dune` dependency additions during integration.
