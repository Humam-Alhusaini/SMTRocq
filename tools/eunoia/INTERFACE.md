# Signature compiler / checked-core boundary

The compiler owns `EoSyntax.v`, `EoRuntime.v`, and `CpcGenerated.v` in
`theories/checker/eunoia/`. It does not edit State, shared dune files, tactics,
or SMTCoq semantics. These modules have no dependency on the checked core.

`EoSyntax.term` is **CPC surface syntax**, not an SMT interpretation:
`Symbol : string -> term`, `Apply : term -> term -> term`. Applications are
curried and implicit type arguments are omitted, as in CPC proof files.
There is no normalization of input formulas. The importer must preserve this
syntax exactly and bind every premise to its checked State entry.

The public entry point is:

```
CpcGenerated.derive : nat -> (term -> option term) ->
  string -> list term -> list term -> option term
```

Arguments are fuel, a partial type query, rule name, explicit arguments, and
ordered premise formulas. Unknown rules, arity/matching/type/side-condition
failures, unmatched helper cases, and exhausted fuel return `None`. `Some t`
is only a syntactic candidate. **It must never authorize a State insertion.**
The checked-core owner must relate the exact premises and `t` to existing
SMTCoq `Atom`/`Form` interpretations using a proved bridge or an existing
verified checker certificate. In particular, the type query is executable
input, not an assumption or semantic oracle; even a malicious query must not
bypass that checked gate. No semantic soundness lemma is claimed here.

Type queries return CPC type syntax (e.g. `Symbol "Bool"`); a sort symbol has
type `Symbol "Type"`. The runtime infers polymorphic binder values from the
types of matched terms, then checks every binder, helper input/output, premise,
and conclusion. Missing type information rejects the step. The bridge should
derive this query from the existing SMTCoq reification tables.

`EoRuntime.run_rule` accepts generated `list (string * rule)` and
`list (string * program)` tables. Rules contain binder type patterns, exact
argument/premise patterns, all equality requirements, and a conclusion
expression. Programs contain typed signatures and ordered pattern/body cases.
There is no rule-name-dependent execution in the runtime.

The coordinator's core API is `eval : rule -> list State.C.t -> option
State.C.t`. Its premises are the fetched, ordered clauses, and its declared
conclusion is compared exactly before a separate small-checker witness gate.
The term/clause adapter must preserve each literal's binding to the shared
Atom/Form tables, including unit/empty clauses, polarity, and any explicit
normalization. Core soundness alone does not prove CPC surface-syntax fidelity.
The proof reader's `src/eunoia/eunoiaProof.{ml,mli}` API is independent.

Build integration: the core owner owns the local `dune` stanza. It should
include these modules under `SMTCoq.checker.eunoia`; their only direct
dependency is `Stdlib`. Imports use that logical prefix. Until then,
`tools/eunoia/check-generated.sh` compiles copies in a temporary directory
using the private smtrocq environment and leaves the worktree clean.
