# Scoped CPC production backend

The backend in `src/eunoia_backend/` now elaborates parser occurrence identities
into nested `EunoiaScope.Next/Push/Discharge` terms and applies the existing
`EunoiaScopedAdapter.checker`, `checker_b`, or `checker_eq` correctness wrapper.
Scope-free proofs retain their existing `EunoiaTactic` path. All paths end in
`Tactics.exact_check`; supplied root hypothesis proof terms remain authoritative.
No scope rule evaluator, semantic axiom, theory change, or proof-valued bypass
is added here.

## Exact scope boundary

Slot allocation is monotonic over roots, pushes, ordinary steps and discharges.
A push saves both the elaborator's binding/proof maps and the backend's clause
map. A pop must have one visible endpoint. Elaboration calls the actual loaded
`CpcGenerated.derive_assuming` on the actual pushed formula, explicit arguments
and that exact endpoint term. Ordinary steps call `CpcGenerated.derive`.
The generated result must match any claimed source conclusion.

The closing payload contains the unguarded endpoint. Its production witness
callback receives only `[S.sort (Lit.neg pushed :: endpoint_clause)]`. Both
ordinary and closing candidates use `Eunoia_witness.Search.produce` in the
integration tests, without a CPC rule-name switch. The concrete scoped checker
reruns generated evaluation, exact premise/assumption/result/root bindings and
the existing multi-operation local semantic gate. Primitive configuration is
fixed to `CpcGenerated.default_primitive`; source proof text cannot select hooks.
Only the fresh exported result survives in the restored parent. Local
assumptions, endpoints and nested exports expire. Every command is visited,
including unused supported/unsupported steps and commands following conflicts.

The root matcher accounts for cvc5 printing identical assertions only once.
It keeps **all** authoritative root terms, clauses, claims, distinct slots and
proof terms. Source assumptions must match either the full ordered list or
its stable first-occurrence projection; they cannot reorder or replace roots. No distinct
formula is removed. This permits supplied tactic tuples that repeat local
hypotheses without weakening checker root binding.

Intermediate carriers can occur solely in function signatures, with no source
equality that registers their `CompDec`. The backend reuses matching actual
context `CompDec` proof terms before table snapshotting. Remaining delayed cuts
are rejected before VM evaluation, with a diagnostic instead of an undeclared
`CompDec0` causing `Not_found`. No missing instance becomes an assumption.

## Strict metadata ingestion

`EunoiaRocq.signature_names` computes names from the loaded generated module's
`cpc_signature_names` inventory (347 names in the current snapshot). This admits
required `@list`/`@list.nil` metadata and
canonical equivalents without accepting arbitrary unresolved identifiers.
These are syntax admissions, not acceptance of a rule or an object formula.
Generated derivation and semantic binding still run for every inference.
Unknown unused symbols/rules, quoted numeric identifiers, signature/exported
name shadowing, unrestricted definitions, and directives still reject.
Definitions remain confined to the printer's `@t<digits>` namespace. Lexical
binders cannot shadow known signature names or exported functions/sorts.

The inventory is generated from the 35-file pinned signature closure. Membership
reserves a name and permits its parsing; it does not declare its operators or
rules supported by the evaluator, adapter or semantic gate.
Decimal/rational source literals and object Real formulas still reject here;
this child does not implement an alternative arithmetic parser or normalize
away exact source spelling. Parent metadata type queries are necessary for
`@list` arguments; surface query results use `Symbol "@List"`.

## Wiring and tests

Coordinator integration added `Require EunoiaScopedAdapter` in
`theories/tactics/Tactics.v` before the already registered public tactic runs
on scoped output. The shared wiring commit is `2dc18f5`; the child itself did
not modify the main `src/dune`, grammar, theory or shared tactic file.
The isolated backend test stanza now also loads SMTCoq
for public tactic regressions.

`tests/integration/Proof.v` retains the original four replay proofs, live proof
and rejection controls. New `Qed` proofs cover scoped Boolean equality,
Boolean goals of both polarities, and nested scopes. Two proofs require the
exported implication to reach the final conflict. Negative tactics cover
changed pushed polarity, changed roots, leaked locals, wrong endpoints,
unsupported unused steps, an invalid witness on an unused supported local
step, and an invalid discharge witness. All new exported
checked proofs run `Print Assumptions`.
`tests/integration/Public.v` checks the actual solver on multiple carrier sorts,
repeated supplied hypotheses and predicate transport using list metadata;
missing intermediate instances reject and the surrounding theorem closes.
The signature-metadata replay checks actual generated chain resolution with
`@list` arguments and the production semantic gate. The OCaml suite checks occurrence-to-slot identity, expiration, endpoint
arity, final parent conflict, metadata membership, shadowing, quoted numerals,
expansion limits and the existing private solver resource/cleanup controls.

Validation used the private wrapper, Rocq 9.3.0 and OCaml 4.14.2; no system
installation, network access or external Logos/Ethos reference was used. The
child merged coordinator metadata/witness dependencies through `80474c3`, and
then the separately authorized witness fix `49bdcec`.

The following commands ran from the child worktree. The build and test commands
returned exit 0; logs are `/tmp/eunoia-scoped-backend-final-build.log` and
`/tmp/eunoia-scoped-backend-final-tests.log`.

```sh
/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2 @install \
  src/eunoia_backend/tests/integration/Proof.vo \
  src/eunoia_backend/tests/integration/Public.vo
/home/charles/code/friends/.toolchains/smtrocq-env dune runtest -j2 src/eunoia_backend
/home/charles/code/friends/.toolchains/smtrocq-env rocq check -silent \
  -Q _build/install/default/lib/coq/user-contrib/SMTCoq SMTCoq \
  SMTCoq.eunoia_backend_tests.Proof SMTCoq.eunoia_backend_tests.Public
python3 tools/audit-eunoia-assumptions.py \
  --import SMTCoq.eunoia_backend_tests.Proof \
  --import SMTCoq.eunoia_backend_tests.Public \
  --theorem scoped_replay_reflexive \
  --theorem nested_scoped_replay_reflexive \
  --theorem scoped_export_required \
  --theorem nested_scoped_export_required \
  --theorem scoped_export_false \
  --theorem signature_metadata_replay \
  --theorem backend_multiple_sorts \
  --theorem backend_duplicate_root_proofs \
  --theorem backend_list_metadata_live \
  --output-dir /tmp/eunoia-scoped-backend-final-assumptions
```

Kernel/audit results: see `/tmp/eunoia-scoped-backend-final-kernel.log`,
`/tmp/eunoia-scoped-backend-final-audit.log`, and the audit's `summary.json`.
No production soundness lemma is added by this child; existing checker
theorems and their baseline Uint63/PArray and proof-irrelevance dependencies
justify the installed proof terms.

Still incomplete: acceptance of a full actual **scoped solver fixture**, live
scoped coverage, complete generated namespace inventory and rules, rational
metadata ingestion, object Real support, broad QF_UF/QF_LIA coverage and
performance evidence. Hand-written CPC scope replays are labeled as such;
they are not represented as solver-produced scope coverage.
