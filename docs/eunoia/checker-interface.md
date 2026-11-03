# Reflective checker interface

Status: core implementation in progress; no CPC coverage or end-to-end backend
is claimed here. This interface is independent of generated rule constructors.

`EunoiaChecker` uses existing `State.S.t`, `State.C.t` and `Terms.Form` literal
indices. A generated adapter supplies `eval : rule -> list C.t -> option C.t`.
The rule payload includes the generated arguments; the core supplies the actual
premise clauses, in the declared order. Unknown or unsupported rules return
`None`. The adapter must perform the signature-generated side conditions. The
core contains no CPC rule-name switch and introduces no SMT-LIB interpretation.

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
argument, not a new axiom. The concrete bridge will discharge it using
`MainChecker.Euf_Checker.step_checker_correct`. Generated evaluation alone is
never trusted as semantic evidence.

The intended initial bridge accepts a **single** existing SMTCoq small-checker
step. Its read footprint must be exactly the step's declared premise list,
and its output must be exactly the generated result. It has no access to other
proof-state clauses, extra assumptions, or an independent whole-proof refutation.
This witness language describes existing semantic checkers, not CPC rules.
Unsupported witness shapes fail closed. Additional witness shapes need their
own precise read-footprint gate.

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
