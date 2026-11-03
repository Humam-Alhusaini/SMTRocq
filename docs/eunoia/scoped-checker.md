# Verified scope checking

`theories/checker/eunoia/EunoiaScope.v` provides a separate scope-aware checker
over the existing `EunoiaChecker.machine`, `State.S`, `State.C`, `Lit`, `Atom`,
and `Form` semantics. It does not modify the scope-free checker, generated
signature, adapter, semantic bridge, tactics, or shared dune files. This is a
verified scope mechanism, not an end-to-end CPC backend.

## Execution and proof boundary

The generic API takes three executable callbacks:

```coq
eval       : rule -> list C.t -> option C.t
scope_eval : scope_rule -> _lit -> C.t -> option C.t
gate       : list C.t -> C.t -> witness -> bool
```

`rule`, `scope_rule`, and `witness` are arbitrary types. There are no CPC rule
names or manually implemented CPC rules in the scope checker. `eval` is the
ordinary generated-evaluator adapter. `scope_eval payload a c` must run the
generated evaluator with the **actual pushed literal** `a` as its assumption
and the **exact local endpoint clause** `c` as its sole premise. Its result
must equal the declared export clause literally. These callbacks have no
semantic soundness hypothesis: every accepted result also needs `gate`.

The nested certificate datatype has these constructors:

```coq
Done
Next : EunoiaChecker.step -> trace -> trace
Push : clause_id -> _lit -> trace -> option discharge -> trace -> trace
```

`Push slot a body closing rest` saves the current parent machine, stores the
unit clause `[a]` in a fresh, in-bounds local slot, and checks `body`. `None`
for `closing` represents an unclosed scope and returns `None`, never a partial
success. `discharge` records an endpoint, export slot, generated-rule payload,
declared conclusion, and semantic evidence. A malformed unmatched pop has no
constructor; the frontend/elaborator must reject it. A missing endpoint is
rejected by the checker itself.

Every `Next` calls the existing `EunoiaChecker.check_step` unchanged, including
its ordered live-premise fetch, generated-result equality, semantic gate,
canonical clause/literal checks, and fresh destination check. Every body and
continuation must succeed completely; a conflict does not terminate checking
early or hide unknown unused steps.

At pop, `close`:

1. Fetches exactly `[endpoint]` from the finished local machine. Missing,
   expired, and out-of-bounds endpoints fail.
2. Runs `scope_eval payload a c` on that exact endpoint clause and pushed
   literal. Failure and a generated/declaration mismatch fail closed.
3. Constructs `guarded a c := S.sort (Lit.neg a :: c)`, whose validity is proved
   under the parent assumptions. `S.sort_correct` establishes its semantics;
   sorting here does not alter the clause supplied to the generated evaluator.
4. Checks `gate [guarded a c] declared evidence`. This gate has **only** the
   guarded clause as its premise, with no access to local clauses or the pushed
   assumption as an unguarded fact.
5. Calls `store` on the saved **parent** machine, inserting only the exact
   generated and gated conclusion. The export slot must be fresh in the parent,
   in bounds, and its clause canonical and well formed. Execution then checks
   `rest` in this restored machine.

`close_binding` exposes the exact endpoint fetch, evaluator equality, gate
acceptance, parent store, exported readback, and
`live next = export_slot :: live parent`. Thus branch-local slots cannot become
premises after pop. The runtime may reclaim a discarded local slot for a later
fresh parent occurrence; the elaborator must map parser occurrence IDs to the
new binding, never resurrect an expired parser occurrence through slot reuse.
Keeping a globally injective occurrence-to-slot map is also supported.

The conditional invariant is:

```coq
active rho assumptions := Forall (fun a => Lit.interp rho a = true) assumptions
invariant rho assumptions m :=
  active rho assumptions -> EunoiaChecker.invariant rho m
```

`push_invariant` proves preservation under the extended assumption list.
`run_invariant` proves preservation across nested scopes and ordinary nodes.
For a local result `c`, `guarded_valid` proves that
`(Lit.interp rho a = true -> C.valid rho c)` entails validity of the guarded
clause, using Boolean case analysis and `Lit.interp_neg`. Even a false local
assumption is safe: a local empty clause yields its negation as a guard, not
an empty clause in the parent. No local assumption is loaded into global roots.

`checker_correct` proves refutation of the authoritative roots, given valuation
wellformedness and the existing generic `gate_sound` proposition. These are
explicit theorem premises, not new declared assumptions. `table_checker`
instantiates the gate with `EunoiaBridge.gate` and checks **all three** of
`Form.check_form`, `Atom.check_atom`, and `Atom.wt t_i t_func t_atom` at runtime.
`table_checker_correct` therefore needs no external typing premise.

`checker_b l b capacity claims trace goal` builds the authoritative root list
`[[if b then Lit.neg l else l]]` itself, then compares certificate root claims
exactly through `load_roots`. Its correctness theorem concludes
`Lit.interp (EunoiaBridge.valuation ...) l = b`. The caller must supply the
reflected user literal and requested polarity authoritatively. This is not a
proof of the future tactic's reification or importer correctness. Multiple
authoritative input clauses use `table_checker` and its refutation theorem.

## Required generated-evaluator extension and adapter wiring

The concrete reference is cvc5 1.4.2's pinned signature:

```
/home/charles/code/friends/.toolchains/cvc5-1.4.2/cvc5-cvc5-1.4.2/proofs/eo/cpc/rules/Builtin.eo
```

Its `scope` declaration has `:assumption F`, one premise `G`, and conclusion
`(=> F G)`. `process_scope` is an ordinary signature rule with a helper program;
it must remain an ordinary `Next` and must be evaluated and gated in full.
These facts describe the integration contract; neither name is special-cased
by `EunoiaScope`.

The existing `CpcGenerated.derive` API takes only arguments and premises.
Its current generated `EoSyntax.rule` does not represent `:assumption`, so it
cannot implement the required scope callback yet. The generator owner should
extend the generated rule schema with an optional assumption pattern, retain
the actual signature declaration, and expose a generic entry point such as:

```coq
derive_with_assumption : nat -> (term -> option term) ->
  string -> list term -> option term -> list term -> option term
(* fuel, type query, rule name, explicit arguments, actual assumption,
   ordered actual premise terms *)
```

This API is a requested interface, not a function implemented in this change.
The runtime must match the supplied assumption against the generated pattern
in the same binder environment as arguments and premises, then validate all
typing and generated requirements before evaluating the conclusion. Missing,
extra, or mismatching assumptions must fail. Ordinary `derive`/`eval` must
reject an assumption-bearing rule used outside a scope. No default assumption,
rule-name switch, or hand-written implication constructor can substitute for
signature generation.

The consuming adapter's concrete callback is:

```coq
scope_eval : scope_payload -> _lit -> C.t -> option C.t
```

It must encode `a` and `c` using the same authoritative SMTCoq tables and exact
CPC term provenance as ordinary premise encoding, call the generated entry
point with `Some encoded_a` and `[encoded_c]`, and faithfully decode/bind the
result to the declared clause. It must preserve unit/empty/disjunction/polarity
encodings and the optional source conclusion. The checker compares that exact
result again. Encoding the guarded clause as the generated premise would lose
the actual CPC scope-rule boundary and is forbidden by this API contract.

The parser's `Assume_push`/`Step_pop` nesting maps to `Push`/`discharge`;
source occurrence identities map explicitly to checker slots. A pop must have
the generated rule's required assumption and one checked endpoint. Unclosed
scopes map to rejection (`closing = None` is available for this); no source
command or unknown rule may be omitted when constructing the nested trace.
The parser handles expired names, but that alone is not scope soundness.

Semantic evidence must prove the generated conclusion from precisely the
guarded clause. The concrete table wrapper currently uses the existing
single-step `EunoiaBridge` witness. A CPC implication encoded as a formula-table
unit may need a separately proved local composition of existing CNF/resolution
checkers to transform the guarded clause into that exact unit. Unsupported
evidence fails; the checker does not export an ungated implication. The generic
checker can also take a richer gate accompanied by its proved `gate_sound`.
No adapter/generator/local-gate files are owned or changed here.

## Compiled regression tests and local verification

`EunoiaScopeTests.v` contains 36 kernel-checked computational examples. Its
deliberately untrusted evaluators are test fixtures, not CPC rule implementations;
all acceptance examples use the actual `EunoiaBridge` semantic gate. They cover:

* Two nested scopes whose exported guard is required by the final resolution.
* Missing, expired, and wrong live endpoints; changed pushed assumptions;
  generated-result mismatches and semantic-output mismatches.
* Escaping inner results, outer results, assumptions, and local conflicts.
* Wrong roots/goals, unknown unused steps (also after local/global conflicts),
  unclosed outer/inner scopes, overwritten parent slots, and malformed pushes.
* An actually false local assumption deriving a local contradiction, exporting
  only its valid guard, and failing to refute the parent or export false.
* Goal/polarity binding, malformed formula/atom tables, and a structurally
  wellformed but ill-typed atom table rejected specifically by runtime typing.

Commands from the repository root, through the private toolchain:

```sh
/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2 theories/checker/eunoia/EunoiaScopeTests.vo
/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2 theories
/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2 @install
/home/charles/code/friends/.toolchains/smtrocq-env dune runtest -j2 theories/checker/eunoia
```

All returned exit code 0. Logs are `/tmp/eunoia-scope-tests-build.log`,
`/tmp/eunoia-scope-theories-build.log`, `/tmp/eunoia-scope-install-build.log`,
and `/tmp/eunoia-scope-runtest.log`. The existing `runtest` alias does not yet
depend on the new tests: their explicit `.vo` build above is required and
executes every example. The coordinator should add `EunoiaScopeTests.vo` to
the existing local `runtest` dependencies; the theory stanza discovers the new
modules automatically. No parent/shared dune or tactic file was changed.

Every new lemma/theorem ends up audited by an embedded `Print Assumptions`.
Reproduce the separate comparison against the existing checker baseline with:

```sh
python3 tools/audit-eunoia-assumptions.py \
  --import SMTCoq.checker.MainChecker \
  --import SMTCoq.checker.eunoia.EunoiaScope \
  --theorem EunoiaScope.guarded_valid \
  --theorem EunoiaScope.close_binding \
  --theorem EunoiaScope.close_invariant \
  --theorem EunoiaScope.push_invariant \
  --theorem EunoiaScope.run_invariant \
  --theorem EunoiaScope.checker_correct \
  --theorem EunoiaScope.table_checker_correct \
  --theorem EunoiaScope.checker_b_correct \
  --theorem Euf_Checker.step_checker_correct \
  --output-dir /tmp/eunoia-scope-assumptions
```

This audit returned exit code 0: all eight new lemmas/theorems have no assumptions
beyond the checked-in baseline. The concrete table/goal theorems have the same
52 dependencies as `Euf_Checker.step_checker_correct`; the generic refutation
theorem uses 23 of them. The generated assumption report and compiler output
are retained outside the repository in that directory. No proof holes or new
assumptions are introduced.

Still incomplete: generated `:assumption` support, the faithful scoped
term/clause adapter, concrete CPC scope/process-scope semantic witness
construction, source-command-to-trace integration, test-alias wiring, tactic
integration, real LIA CPC acceptance, coverage measurements, and benchmarks.
