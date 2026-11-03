# Reflective checker interface

Status: core and initial semantic bridge compiled and proved; no CPC coverage
or end-to-end backend is claimed here. This interface is independent of
generated rule constructors.

`EunoiaChecker` uses existing `State.S.t`, `State.C.t` and `Terms.Form` literal
indices. A generated adapter supplies `eval : rule -> list C.t -> option C.t`.
The rule payload includes the generated arguments; the core supplies the actual
premise clauses, in the declared order. Unknown or unsupported rules return
`None`. The adapter must perform the signature-generated side conditions. The
core contains no CPC rule-name switch and introduces no SMT-LIB interpretation.
An arbitrary evaluator cannot bypass the proved semantic gate, but fidelity to
the CPC signature still requires the separate generated adapter described below.

Each step contains a fresh destination slot, premise slot indices, a rule
payload, a declared clause, and a semantic witness. The core:

1. Rejects out-of-bounds, uninitialized and forward premise references.
2. Runs `eval` on exactly the fetched premise clauses, without fallback.
3. Requires literal-for-literal equality of its result and the declared clause.
4. Rejects malformed clauses: literal variables must be in the existing formula
   table, and the clause must already equal `S.sort` of itself. Canonical clauses
   avoid silently changing the exact clauses exposed to the evaluator.
5. Runs the semantic gate on those same premises and conclusion.
6. Writes the clause through `S.set_clause` only after every check succeeds;
   rejects duplicate destinations and propagates failure through the whole trace.

The generic soundness theorem quantifies over a gate together with a proof that
acceptance preserves the existing clause interpretation. This is a theorem
argument, not a new axiom. The concrete bridge discharges it using
`MainChecker.Euf_Checker.step_checker_correct`. Generated evaluation alone is
never trusted as semantic evidence.

The initial bridge accepts a **single** existing SMTCoq small-checker
step. Its read footprint must be exactly the step's declared premise list,
and its output must be exactly the generated result. It has no access to other
proof-state clauses, extra assumptions, or an independent whole-proof refutation.
This witness language describes existing semantic checkers, not CPC rules.
Unsupported witness shapes fail closed. Additional witness shapes need their
own precise read-footprint gate. `EunoiaBridge.witness` contains an existing
`Checker_Ext.step` and a scratch capacity. `decode` supports resolution,
weakening, flattening, the basic CNF constructors, EUF transitivity/congruence,
Micromega/disequality, arithmetic splitting and distinct elimination; bit-vector
and array witness shapes currently fail. It converts supported witnesses to
`Euf_Checker.step` without exposing `Hole` or `ForallInst`.

`prepare` loads the supplied premise clauses into fresh scratch slots listed by
the witness footprint, and reads them back for exact ordered equality, including
length. Repeated scratch indices, extra reads hidden by `List.combine`, and a
non-fresh or out-of-bounds output are rejected. Witness builders can use a
distinct scratch slot for each occurrence of a repeated global premise. Only
one existing checker step executes, and its output clause must exactly equal
the declared/generated conclusion. `gate_binding` exposes these equalities;
`gate_correct` proves semantic validity from those premises alone.

This first bridge intentionally supports only conclusions directly produced by
one existing checker step. For example, an EUF checker may produce a tautological
clause containing negated equality premises, while CPC derives a unit equality
from asserted equality premises. Those are different exact clauses: this gate
rejects that use until a proved consequence bridge (or a separately checked
local composition with the same premise boundary) is supplied. Listing an EUF
witness shape above does not establish coverage of a similarly named CPC rule.

`EunoiaBridge.checker` checks `Form.check_form` and `Atom.check_atom`, and its
soundness theorem requires the existing `Atom.wt` proof for the interpretation
tables, just like `Euf_Checker` soundness. It does not invent a typing axiom or
claim an unverified importer has established typing. The bridge's assumption
audit inherits Uint63 primitives and the existing proof-irrelevance dependency
of `Euf_Checker.step_checker_correct`; no new assumptions are declared.

The caller supplies authoritative roots as existing SMTCoq clauses. Certificate
root claims pair slots with clauses; their order, number, and literal sequences
must match the authoritative roots exactly. Slots must be fresh, in bounds, and
clauses canonical and well formed. The final conflict slot must have been
initialized and contain the empty clause. Invalid goal indices cannot read an
array default. A tactic proving a user goal must bind its negation in the
authoritative roots; the core proves refutation of those roots only.

The coordinator owns generated adapter wiring, parent theory dependencies and
tactic integration. Only an isolated `theories/checker/eunoia/dune` stanza is
owned here. The final integration must audit the adapter's term/clause encoding
and generated evaluator separately; core soundness does not claim that a
particular generator implements CPC.

## Generator coordination (2026-11-03)

The generator's early `tools/eunoia/INTERFACE.md` defines `EoSyntax.term` as
`Symbol string | Apply term term`, and exposes:

```
CpcGenerated.derive : nat -> (term -> option term) ->
  string -> list term -> list term -> option term
```

The arguments are fuel, a partial type query, the rule name, explicit arguments,
and exact ordered premise terms. The result is syntax only. A separate faithful
adapter is still required: it must encode each fetched `C.t` using the existing
SMTCoq atom/form tables, preserving its relationship to the original CPC surface
term, run `derive`, and check the returned term against the exact declared
`C.t`. Disjunctions, unit clauses, empty clauses, polarity, implicit typing,
and normalization must have explicit checked encodings; a permissive or lossy
decoder is insufficient. The type query must be derived from the reification
tables and must not be treated as a semantic oracle. This adapter is not
implemented by the core or bridge yet. It will instantiate the abstract `eval`
argument. Until it is integrated, the core's theorem establishes refutation of
the caller's SMTCoq roots, not fidelity of a CPC file or of SMT-LIB reification.

The proof reader is owned separately in `src/eunoia/eunoiaProof.{ml,mli}`.
There is no runtime dependency on it or on generated modules in this work.

## Local verification and integration

`EunoiaCheckerTests.v` contains 35 kernel-checked computational examples (one
positive resolution case and 34 rejection cases). Its deliberately untrusted
test evaluator includes unknown rules and arbitrary returned clauses; these
exercise the real semantic gate and are not a CPC adapter. Tests cover premise
order and indices, root identity/count/slots, destination freshness, unknown
steps before and after a conflict, goal binding, canonical/literal bounds,
witness footprints, output mismatches, and invalid formula tables. The isolated
directory's `runtest` alias depends on the compiled test module.

The following commands passed with exit code 0 through the private environment:

```
/home/charles/code/friends/.toolchains/smtrocq-env dune build theories/checker/eunoia
/home/charles/code/friends/.toolchains/smtrocq-env dune build theories
/home/charles/code/friends/.toolchains/smtrocq-env dune runtest theories/checker/eunoia
/home/charles/code/friends/.toolchains/smtrocq-env dune runtest
```

Every new soundness lemma has an embedded `Print Assumptions` command. A separate
audit compared the two top-level bridge theorems and the generic refutation
theorem with `Euf_Checker.step_checker_correct`: the bridge has the same 52
reported foundational assumptions as that existing theorem, while the generic
refutation theorem uses a subset of 16. There are no additional assumptions.

No parent `theories/dune`, `theories/checker/dune`, or tactic stanza was changed.
The coordinator should reuse the isolated `SMTCoq.checker.eunoia` theory stanza
when integrating generated modules, and add that theory to any tactic module
that imports it. The faithful term/clause adapter, concrete CPC witness
construction, full CPC coverage, tactic/root reification proof, and benchmarks
remain incomplete. Scratch-state construction and linear live-slot membership
have not been benchmarked.
