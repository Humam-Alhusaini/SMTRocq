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

`derive = derive_with no_extension`. The hook implements generic EO literal
operations, not CPC rules. It receives evaluated **internal** syntax arguments
and returns internal syntax or `None`. Native Booleans, literal predicates and
operator-aware list operations are supplied by the runtime. Unimplemented
arithmetic, bit-vector, string, datatype and comparison primitives fail closed.
The manifest records all referenced native operations; full helper bodies and
all source includes are retained even for branches that reach an unavailable
primitive. An arithmetic extension should implement exact signed/rational
literal arithmetic here, leaving relation tables, polynomial algorithms and
rule guards generated from `.eo`. Dependent arithmetic nil elaboration remains
a separate required extension; the hook alone does not enable those operators.

## Build ownership

No core, adapter, semantic bridge, tactic, or dune file is changed. The existing
public `derive` API lets the coordinator use the merged adapter unchanged.
`tools/eunoia/check-generated.sh` compiles isolated copies, regenerates from the
vendored byte-identical cvc5 signature, replays all actual UF fixture steps,
and independently kernel-rechecks the tests. Semantic certificate coverage,
reader/tactic wiring, and full port completion remain coordinator-owned work.
