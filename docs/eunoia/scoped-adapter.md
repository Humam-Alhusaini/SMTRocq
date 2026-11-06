# Concrete generated scoped adapter

`theories/checker/eunoia/EunoiaScopedAdapter.v` composes the existing
`EunoiaScope` scope machine, `EunoiaAdapter` table encoding, actual
`CpcGenerated` evaluator, and multistep `EunoiaLocal.gate`. It supplies concrete
refutation, Boolean-goal and Boolean-equality checker correctness theorems.
This layer is implemented and checked; production scoped CPC import, evidence
construction and tactic wiring remain coordinator work.

## Generated boundary and exact binding

Both ordinary and closing nodes use `EunoiaAdapter.rule_payload`:

```coq
Payload rule_name explicit_arguments ordered_premise_terms result_term result_clause
```

`eval fuel` is definitionally the existing `EunoiaAdapter.eval` with the same
authoritative tables and naming. It retains ordinary source evaluation,
including exact premise ordering and generated-result binding. In particular,
ordinary `derive` rejects assumption-bearing rules; `process_scope` is an
ordinary node evaluated from its generated declaration and helper programs.

`scope_eval fuel payload actual_pushed_literal exact_local_endpoint_clause`:

1. Checks `tables_wf`, including names, `Form.check_form`, `Atom.check_atom`,
   and `Atom.wt`.
2. Binds **exactly one** premise, the endpoint clause, against the payload's
   ordered premise terms through `EunoiaAdapter.bind_terms`. Missing and extra
   premises fail. Empty clauses encode as `false`, units retain their exact
   literal encoding, and disjunctive clauses retain canonical order and polarity.
3. Calls `encode_literal` on the actual pushed literal using the same tables.
   No certificate field supplies an alternative assumption.
4. Calls `CpcGenerated.derive_assuming` with that pushed formula **before**
   explicit arguments, followed by the exact bound local premise list. The
   generated declaration matches the assumption, arguments, premises, typing
   and requirements in its binder environment. No rule name is special-cased.
5. Requires literal equality between the generated term and payload result
   term, and binds the payload result clause to that same generated term.
   Returns precisely that clause.

The implementation factors this through `scope_eval_with default_primitive`,
which calls `derive_assuming_with default_primitive`; these are definitionally the
public generated `derive_assuming`. `scope_eval_with_binding` exposes the
actual encoded assumption, exact premise binding, generated result equality,
and exact result clause. `close_with_binding` additionally exposes the local
endpoint fetch, semantic gate, parent store, export readback and restored live
set. Encoding a guarded clause as the generated premise is never done.

The existing clause adapter deliberately permits a surface disjunction to
bind either a table-backed disjunction unit or the corresponding canonical
clause. The actual checker clause and endpoint remain exact: the scope machine
fetches one specific live clause, the payload binds its surface encoding, and
the semantic gate receives the guard formed from that actual clause. There is
no semantic normalization or guessed inverse decoding in this adapter.

## Semantic evidence and nested backend API

The public certificate types are:

```coq
EunoiaScopedAdapter.trace
  = @EunoiaScope.trace rule_payload rule_payload EunoiaLocal.witness
EunoiaScopedAdapter.discharge
  = @EunoiaScope.discharge rule_payload EunoiaLocal.witness

Done
Next (Step destination ordered_premise_slots payload declared_clause witness) rest
Push fresh_assumption_slot actual_literal body (Some discharge) rest
Discharge local_endpoint fresh_parent_export payload declared_clause witness
```

Here `rule_payload` abbreviates `EunoiaAdapter.rule_payload`. The generated
input to a discharge is the exact endpoint. Its **semantic** input is solely
`[EunoiaScope.guarded actual_literal endpoint_clause]`. The witness cannot use
an unguarded local assumption, local conflict, or arbitrary local clause as a
parent fact. `EunoiaScope.close` checks equality with the declared clause,
passes that exact result to `EunoiaLocal.gate`, and stores it in the saved
parent machine. Only the exported slot joins the parent's live set; body
slots disappear, including inner exports when the outer scope closes.

An `EunoiaLocal.Witness capacity root_claims program conflict_slot` must prove
the exact consequence by refuting:

```coq
EunoiaLocal.local_roots premises conclusion
  = premises ++ map (fun l => [Lit.neg l]) conclusion
```

Every `Command existing_Checker_Ext_operation expected_clause` is decoded and
executed by existing SMTCoq checkers. Live reads, fresh bounded output,
canonical expected clause, exact computed output and fallback rejection are
checked. The entire program runs, including unused trailing commands. This
is the existing multistep gate and its `gate_correct` proof, not the earlier
single-operation bridge. The witness is data, with no proof-valued bypass.

For production import, the backend must:

* Map parser occurrence identities to live checker slots and preserve every
  source command, including unsupported or unused commands. Reject unmatched
  pops and expired occurrence references; use `None` for an unclosed push.
* Reify the actual pushed formula, every endpoint and generated result into
  the authoritative tables; retain exact source terms in each payload.
* Map nested `Assume_push` / `Step_pop` commands to `Push` / `Discharge`, choose
  fresh exports in the saved parent, and retain source premise order.
* Construct local evidence for each ordinary result and each guarded export.
  The tests demonstrate CNF projection and binary resolution compositions for
  implication units, nested implications and ordinary `process_scope` output.
* Invoke the concrete checker with authoritative roots or reflected user goal,
  then discharge with the corresponding correctness theorem. Root terms and
  certificate claims are compared with those roots at runtime.

`run` exposes execution over an existing `EunoiaChecker.machine` for backend
inspection. Successful `run` alone is not a refutation theorem: the public
`checker` also loads exact roots and checks a live empty goal clause.
`checker_b` constructs the opposite-goal root via `EunoiaTactic.goal_roots`.
`checker_eq` follows the existing signed `Fiff` convention: a negative iff
literal, with exact ordered children matching the two authoritative literals.
All three default checkers have complete correctness proofs without an
external gate or typing hypothesis.

The `_with` entry points accept an `EoRuntime.primitive_hook`, but still invoke
`CpcGenerated.derive_with` / `derive_assuming_with` and the same semantic gate.
They never accept a replacement rule evaluator. Their correctness theorems
also require no hook soundness assumption because every result is independently
semantically gated. A future arithmetic backend must fix its hook to verified
language primitives in backend code; neither the proof file nor parser data
may select it. Public defaults use `CpcGenerated.default_primitive`, matching
ordinary generated derivation. That fixed configuration dispatches the
implemented literal operations and term ordering; explicit `_with` calls can
still use `no_extension` to test missing-primitive rejection.

## Compiled evidence

`EunoiaScopedAdapterTests.v` contains 59 examples, including five semantic
consequences proved through the new correctness wrappers. These are honestly
hand-produced local certificates, not cvc5 output or live tactic integration.
Every rule computation uses the actual generated evaluator. They cover:

* Source `scope` and ordinary `process_scope`, including full multistep
  semantic discharge and final checked refutation.
* Two nested scopes exporting `p => (q => false)`, then generated
  `process_scope false` producing `not (and p q)`; the export is required by
  the final refutation. Both closing gates and processing gate are computed.
* Canonical disjunctive endpoints, Boolean goals of both polarities, signed
  equality goals and exact restoration of the parent live set.
* Changed pushed formula/polarity, endpoint clause/slot, generated output,
  result clause, declared output, missing/extra premise and unsupported rule.
* Leaked local assumptions, local conflicts, inner exports and unguarded local
  certificate roots; unclosed outer/inner scopes; unused unsupported steps
  before/after local or global conflicts.
* Changed authoritative root terms/claims, goal/polarity/iff children, malformed
  tables, structurally valid but ill-typed atoms, and exhausted encoding fuel.

Exact commands, run from the repository root with no system installation:

```sh
/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2 theories/checker/eunoia/EunoiaScopedAdapter.vo
/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2 theories/checker/eunoia/EunoiaScopedAdapterTests.vo
/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2 @install theories
/home/charles/code/friends/.toolchains/smtrocq-env dune runtest -j2 theories/checker/eunoia
/home/charles/code/friends/.toolchains/smtrocq-env rocq check -silent \
  -Q _build/install/default/lib/coq/user-contrib/SMTCoq SMTCoq \
  SMTCoq.checker.eunoia.EunoiaScopedAdapter \
  SMTCoq.checker.eunoia.EunoiaScopedAdapterTests
python3 tools/audit-eunoia-assumptions.py \
  --import SMTCoq.checker.eunoia.EunoiaScopedAdapter \
  --import SMTCoq.checker.eunoia.EunoiaScopedAdapterTests \
  --theorem EunoiaScopedAdapter.scope_eval_with_binding \
  --theorem EunoiaScopedAdapter.close_with_binding \
  --theorem EunoiaScopedAdapter.checker_with_binding \
  --theorem EunoiaScopedAdapter.checker_with_correct \
  --theorem EunoiaScopedAdapter.checker_correct \
  --theorem EunoiaScopedAdapter.checker_b_with_correct \
  --theorem EunoiaScopedAdapter.checker_b_correct \
  --theorem EunoiaScopedAdapter.checker_eq_with_correct \
  --theorem EunoiaScopedAdapter.checker_eq_correct \
  --theorem EunoiaScopedAdapterTests.single_refutation \
  --theorem EunoiaScopedAdapterTests.nested_refutation \
  --theorem EunoiaScopedAdapterTests.boolean_goal_correct \
  --theorem EunoiaScopedAdapterTests.equality_goal_correct \
  --theorem EunoiaScopedAdapterTests.negative_boolean_goal_correct \
  --output-dir /tmp/eunoia-scoped-adapter-assumptions
```

Logs: `/tmp/eunoia-scoped-adapter-{build,tests-build,install-build,runtest,kernel,audit}.log`;
assumption details: `/tmp/eunoia-scoped-adapter-assumptions/summary.json`.
All six commands above returned exit code 0, including the independent recursive
kernel recheck (silent success). All nine new adapter lemmas/theorems include `Print Assumptions`, as do the
five semantic test consequences. The audit compares all fourteen against
`docs/eunoia/baseline-assumptions.txt`; the audit passed with no assumptions beyond that existing checker baseline.
The scope and close binding lemmas use 16 and 18 existing dependencies; the
root/table binding lemma uses 17; semantic wrappers and consequences use the
existing 52 dependencies, including primitive arrays/integers and proof
irrelevance. This is baseline-relative soundness, not an axiom-free claim.

The coordinator should add `EunoiaScopedAdapterTests.vo` to the existing
`runtest` alias in `theories/checker/eunoia/dune`. The new modules are already
discovered by the existing theory stanza, so no new stanza is needed. Until
that alias change, the explicit tests `.vo` target above is required. This
child changes only the adapter, its tests and this document, with no shared
dune/tactic/backend/generator/runtime/local-gate edits.

Still incomplete: production scoped parser-to-trace elaboration, automatic
local evidence construction for solver traces, backend nesting and scoped
tactic invocation, fixed arithmetic primitive hook integration, full CPC
coverage, broader LIA integration, performance measurement and benchmarks.
The scope-free live tactic probes owned by the coordinator do not establish
live scoped integration here. No overall port completion is claimed.
