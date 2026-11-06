# Goal-bound checker entry points

`EunoiaTactic.v` fixes the generated adapter to `EunoiaLocal.gate`. It uses the
same existing interpretation tables for syntax binding and every local semantic
certificate. There is no gate-soundness assumption supplied by the plugin: the
concrete wrapper discharges it with `EunoiaLocal.gate_correct`, after extracting
`Atom.wt` from the adapter's executable table checks.

The public entry points are in module `EunoiaTactic`:

* `checker` and `checker_correct`: checked refutation of authoritative clauses,
  with CPC root terms and root claims checked by the adapter.
* `checker_b` and `checker_b_correct`: arguments are the four tables, names,
  fuel, capacity, goal literal `l`, requested Boolean result `b`, CPC root terms,
  root claims, trace, and conflict slot. The authoritative clauses are constructed
  inside the checker as `[[if b then Lit.neg l else l]]`; the file cannot select
  a different theorem. Acceptance proves `Lit.interp valuation l = b`.
* `checker_eq` and `checker_eq_correct`: after the common arguments, supply the
  left and right literals and the negative literal of their `Form.Fiff` node.
  The wrapper checks polarity, node shape and both child indices. Acceptance
  proves equality of the left/right Boolean interpretations, following the
  existing SMTCoq equality-proof convention.

The trace payload is `EunoiaAdapter.rule_payload`; its evidence type is
`EunoiaLocal.witness`. All signature-derived computations, exact term/clause
bindings, live/fresh slot checks, and local semantic operations remain mandatory.
The wrappers do not parse files, invoke cvc5, generate witnesses, or reify goals.
The OCaml proof builder must pass the original reified literal and tables and
use one of these correctness lemmas with a kernel-checked computation result.
The wrapper is currently scope-free. The separate `EunoiaScope` mechanism
still needs concrete generated-assumption and adapter wiring for scoped proofs.

`EunoiaTacticTests.v` has 14 compiled examples. A two-step generated `refl` /
`contra` trace, with complete local semantic witnesses, proves a table-backed
reflexivity goal through `checker_b_correct`. The other examples check goal,
polarity, root, premise, conflict, unused-step, and equivalence-shape rejection.
This is reflective-checker evidence, not a cvc5-generated proof or an operational
Rocq tactic. Actual backend replay remains a separate completion requirement.

Validation on the integration branch:

```sh
/home/charles/code/friends/.toolchains/smtrocq-env dune build @install -j2
python3 -B tools/audit-eunoia-assumptions.py \
  --import SMTCoq.checker.eunoia.EunoiaTactic \
  --import SMTCoq.checker.eunoia.EunoiaTacticTests \
  --theorem EunoiaTactic.goal_roots_refute \
  --theorem EunoiaTactic.checker_correct \
  --theorem EunoiaTactic.checker_b_correct \
  --theorem EunoiaTactic.checker_eq_correct \
  --theorem reflected_goal_correct \
  --theorem EunoiaLocal.EunoiaLocal.gate_correct \
  --output-dir /tmp/smtrocq-tactic-wrapper-assumptions
```

Both commands exited 0. The six audits add no dependencies beyond the existing
checker baseline. The full report is retained at the specified path; source
inspection found no proof-hole or new-assumption declarations in these modules.
The equivalence correctness theorem is compiled and audited; the acceptance
example currently exercises the Boolean-result path. Full tactic tests must
also exercise the equivalence path on actual solver output.
