# Local semantic witness producer

The independent library lives in `src/eunoia_witness` (`eunoia_witness`). Its
entry point is `Eunoia_witness.Search.produce ~atoms ~forms ~premises
~conclusion ()`. Both clause arguments use `Common.SmtAtom.Form.t`; premises
are an **ordered list of whole clauses**, not a list of unit assumptions.
Successful output is an untrusted `Certificate.witness` candidate for
`EunoiaLocal.gate`; failure is explicit and must reject the generated step.
No CPC rule name is an input. This producer does not validate CPC derivations.

The supplied atom/form tables belong to the backend and must be the same tables
eventually passed to the verified gate. Search may intern intermediate equality
atoms and forms into them. Serialize the tables **after** all witnesses have
been produced. Input clauses must already be sorted and duplicate free by
`Form.to_lit`; the producer rejects noncanonical input rather than silently
changing the requested implication. Roots preserve premise order and include
one negated singleton for each conclusion literal, exactly as `local_roots`.

`Certificate` mirrors the gate's capacity, root claims, command list (action and
exact expected clause), and conflict slot. It deliberately exposes only the
small-checker operations used by search, with fresh writes and binary resolution.
It never exposes holes or accepts a solver answer as evidence. The backend must
run the verified gate on every candidate; successful search is not acceptance.

No shared dune/tactic edits are required: the backend owner should add
`eunoia_witness` to its own library dependencies. There are no changes to the
generator, adapter, backend, core, or shared source files.

## Search and certificates

Search expands reachable Boolean connectives into the existing `BuildDef`,
`BuildDef2`, and `BuildProj` clauses. It uses indexed binary resolution, prioritizes
units, memoizes clause pairs, and deduplicates clauses. This is bounded resolution
saturation, not truth-table enumeration. It does not call an external solver.
An empty root is already a conflict. Unused local search commands are removed by
following the conflict's read dependencies; all ordered roots remain present.

EUF rounds build a graph from **proved unit equalities**. Breadth-first paths
give `EqTr` certificates, including symmetry and reflexivity. Applications with
the same head and connected corresponding arguments give `EqCgr`; identical
arguments use `None`. Predicate applications give `EqCgrP` in either direction.
Intermediate argument equalities are interned into the shared tables and proved
by `EqTr`. Every theory lemma is a tautology containing the negated equalities
it needs, and ordinary premise resolution discharges those literals. No graph
reachability fact is trusted by the gate.

For an entirely arithmetic implication, each nonunit premise is represented by
an auxiliary `For` formula. `Lia.build_lia_certif` is called on the single local
clause `~premise_1 \/ ... \/ ~premise_n \/ conclusion`, keeping disjunctive
premises intact. CNF equivalences connect these auxiliary formulas to their
original whole-clause roots. Mixed proofs can also use a Micromega conflict
lemma over the currently proved arithmetic units. The Micromega proof object
is stored in `LiaMicromega`; the gate runs the existing LIA checker on it.
The OCaml producer conservatively admits integer comparisons/equalities,
Boolean constants, conjunctions and disjunctions to this arithmetic translation.

The library uses `Common.SmtAtom`/`Form` and `Lia` directly. It does not use
`SmtCnf.MakeCnf` or `SmtTrace`'s global mutable clause allocator: those build
whole-solver traces and are unsuitable for independent per-inference fresh
slots. Instead it emits precisely the same small-checker constructors and
predicts their results. These untrusted predictions are rechecked in Rocq;
they are not a replacement semantics or acceptance checker.

Default per-inference limits are 4,096 clause slots (including roots), 100,000
resolution pairs, 32 theory rounds, 128 reachable atom terms, 256 reachable or
new formula nodes, and 64 formula-node visits per Micromega query. Interned
auxiliary formulas may remain in the tables after failed search; they never
become assumptions. Formula-size limits bound Micromega input, but its existing
API does not expose a wall-clock timeout. Callers needing stronger isolation
should impose a process-level timeout and reject a timed-out inference.

## Rocq serialization

`Certificate.to_coq ~local ~step witness` returns an ordinary Rocq constructor
term, including the native Micromega proof terms via the existing
`RocqInterface.micromega_dump_proof_term`. `local` resolves `Witness`, `Command`,
and `command` in the actual loaded `EunoiaLocal` module. `step` resolves `Res`,
`CFalse`, `CTrue`, `BuildDef`, `BuildDef2`, `BuildProj`, `EqTr`, `EqCgr`, `EqCgrP`, and
`LiaMicromega` in the actual `Checker_Ext` module. These callbacks only resolve
constructors; they do not decide whether a command is valid.

Root claims serialize as `list (uint63 * list uint63)` in exactly input order.
Expected clauses are sorted, duplicate-free literal lists. Slots are fresh and
below capacity, but may have gaps after pruning. `Res (dst,a,b)` serializes to
`Checker_Ext.Res dst` with a primitive array of **length two**, entries `a,b`,
and default zero. `CoqTerms.mkArray` takes an OCaml array whose final entry is
the default, so its input has three entries. The existing resolution checker
computes `C.resolve clause_b clause_a`; its first numeric complementary pair
determines the pivot. The producer mirrors that order, and never emits an
operation predicted to return `C._true` (`[0]`), except the dedicated proved
`CTrue` operation. Other operations still reject that failure fallback.

All tables must be serialized after search and passed unchanged to the gate.
The backend still owns generated derivation validation, premise lookup/order,
conclusion binding, atom typing, and requiring successful semantic gates.
None of these obligations is discharged by `Search.produce` returning `Ok`.

## Tests and remaining coverage

`src/eunoia_witness/tests/search_tests.ml` runs the native producer on exact
positive/negative implications and checks root binding, bounds, fresh slots,
live reads, resolution predictions, and the final empty clause.
`GateProbe.v` and `probe.ml` additionally serialize each positive
candidate, typecheck the resulting gate application, and run the real local
gate with Rocq's VM. They test rejection after corrupting capacity, removing a
root, changing an expected clause, changing the supplied premises/conclusion,
or removing the scaling example's Micromega certificate. This is
test computation, not a proof-producing unchecked cast.

The optional probe script accepts a read-only gate source path, copies it under
`/tmp`, records its SHA256, compiles it, and retains logs there. Run after the
workspace's ordinary build has made its plugin packages available:

```sh
/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2
/home/charles/code/friends/.toolchains/smtrocq-env dune runtest -j2 src/eunoia_witness/tests
bash src/eunoia_witness/tests/verify-local-gate.sh \
  /home/charles/.t3/worktrees/SMTRocq/t3-cf2b9cba/theories/checker/eunoia/EunoiaLocal.v
```

Coverage remains incomplete. EUF propagation uses unit equality paths and does
not implement theory splitting for arbitrary nonunit EUF clauses. Search can
exhaust its budgets on a valid inference. Quantifiers, arrays, BV rules,
distinct elimination, `Fnot2` flattening, and Boolean equality/form bridges are
not implemented. The dedicated `CTrue` path now supports singleton-true
proofs and Boolean equality-to-true rewrites; all other tautology fallbacks
remain rejected. Backend integration and CPC fixture-wide
coverage remain the coordinator's work.

No Rocq soundness lemmas or assumptions are added by this library. The copied
gate runs its own existing `Print Assumptions` commands when compiled; their
output is retained in `gate-assumptions.log`. This is not a new soundness claim
for the backend or a claim of an assumption-free existing checker.

## Local evidence (2026-11-03)

On branch `t3/eunoia-witness-producer`, worktree
`/home/charles/.t3/worktrees/SMTRocq/t3-3895f253`:

* `/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2`: exit 0.
  Initial full build log `/tmp/smtrocq-witness-full-build.log`; final incremental
  build after all implementation/test edits also exited 0, log
  `/tmp/smtrocq-witness-full-build-final.log`.
* `/home/charles/code/friends/.toolchains/smtrocq-env dune runtest -j2 src/eunoia_witness/tests`:
  exit 0, 49 native search cases. Log `/tmp/smtrocq-witness-search-tests.log`.
  A final cached run also exited 0.
* `bash src/eunoia_witness/tests/verify-local-gate.sh /home/charles/.t3/worktrees/SMTRocq/t3-cf2b9cba/theories/checker/eunoia/EunoiaLocal.v`:
  exit 0, same 49 cases (33 positive candidates, 16 negative/input cases),
  with every positive candidate actually serialized,
  typed using `Typing.type_of` (collecting ordinary universe constraints), and
  VM-rechecked by the real gate; deliberate mutations were rejected. Log
  `/tmp/smtrocq-witness-probe-final.log`, complete probe directory
  `/tmp/smtrocq-witness-probe.JTiXEj/`.
* The copied gate's SHA256 is
  `e5ba60662cef8ffdf4b99f5729a8931bb6a4732ea4dd0787f4f2b02ed1e5f9ed`.
  Its existing assumption audit is in
  `/tmp/smtrocq-witness-probe.JTiXEj/gate-assumptions.log`. No new soundness
  lemmas were introduced here, so there are no additional assumptions to print.
* `git diff --check`: exit 0. The forbidden-declaration/proof-hole scan over
  this producer and document returned no matches. No Logos/Ethos source,
  external solver, network access, install, or shared-file modification was
  needed for this task.

These checks establish tested local witness production and replay coverage;
they do not establish overall CPC importer completion.

## Direct SMTCoq theory candidates

`Theory.select` tries compact truth, exact premise reuse, equality transitivity,
congruence, and atomic arithmetic certificates before local search. It uses
actual clauses and formulas, with no CPC rule-name dispatch. Atomic arithmetic
uses the exact canonical conditional clause and existing `Lia.build_lia_certif`.
Pure UF inputs skip Micromega; Boolean expansion retains bounded local search.
`Theory.from_witness` can extract an exact matching arithmetic certificate from
that fallback. `Theory.to_coq` emits ordinary data accepted only by the proved
`EunoiaTheory.gate`; typed native probes recompute every emitted candidate with
that gate. The frontend serializes tables after all producers finish.

The backend wraps these candidates with `EunoiaMemo.Theory` and can share them
through checked `TheoryEntry` values. Every source occurrence still goes through
the full generated checker and actual ordered clause bindings. See
[the architecture and measurements](theory-certificates-2026-11-10.md).
