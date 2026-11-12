# Local semantic certificates for one generated CPC step

This is an executable, proved semantic gate, not an integrated CPC importer or
witness producer. `theories/checker/eunoia/EunoiaLocal.v` is independent of
CPC rule names, the generator, the adapter, and the global proof state. It uses
only existing SMTCoq clauses, formula/atom interpretation, and
`MainChecker.Euf_Checker.step_checker`. No solver is invoked by the gate.

## API and caller obligations

```coq
EunoiaLocal.gate : forall ti (tf : array (Atom.tval ti)),
  array Atom.atom -> array Form.form ->
  list State.C.t -> State.C.t -> EunoiaLocal.witness -> bool

EunoiaLocal.gate_correct : forall ti tf ta tfo,
  Atom.wt ti tf ta ->
  @EunoiaLocal.gate_sound ti tf ta tfo
    (@EunoiaLocal.valuation ti tf ta tfo)
```

The local `gate_sound` definition unfolds to exactly the core's contract:

```coq
forall cs c w,
  @EunoiaLocal.gate ti tf ta tfo cs c w = true ->
  Forall (C.valid (@EunoiaLocal.valuation ti tf ta tfo)) cs ->
  C.valid (@EunoiaLocal.valuation ti tf ta tfo) c.
```

The gate itself checks `Form.check_form` and `Atom.check_atom`. The caller must
still establish the existing `Atom.wt ti tf ta` obligation; it is not a new
assumption declared by this module. The interpretation is exactly
`Form.interp_state_var (Atom.interp_form_hatom ti tf ta)
(Atom.interp_form_hatom_bv ti tf ta) tfo`.

The coordinator can instantiate `EunoiaChecker` with witness type
`EunoiaLocal.witness`, gate `@EunoiaLocal.gate ti tf ta tfo`, and the theorem
`@EunoiaLocal.gate_correct ti tf ta tfo`. That theorem is definitionally
compatible with `EunoiaChecker.gate_sound`; no semantic conversion is needed.
The actual implicit arguments may be supplied with `@` when instantiating it.

Before EVERY invocation, the generated adapter must run signature-generated
`derive` on the exact ordered fetched premises and check the exact conclusion
binding. This gate adds semantic evidence only. It cannot establish signature
fidelity, skipped-step coverage, surface-term encoding, or authoritative user
root binding. Do not replace a CPC trace with one call on a separate whole-goal
solver certificate.

## Witness data and exact local roots

```coq
Record command := Command {
  action : Checker_Ext.step;
  expected : C.t
}.
Record witness := Witness {
  capacity : Uint63.int;
  root_claims : list (clause_id * C.t);
  program : list command;
  conflict : clause_id
}.
```

For the supplied premise clauses `cs` and conclusion clause `c`, the ONLY
initial roots are

```coq
local_roots cs c = cs ++ map (fun l => [Lit.neg l]) c.
```

Each premise remains one clause. For example, `[[p;q]]` supplies `p OR q`,
never separate assumptions `p` and `q`. Negating a conclusion clause is a
conjunction of negated units: conclusion `[p;q]` adds roots `[neg p]` and
`[neg q]`. A formula conclusion, including a disjunction or Boolean equality
represented by a formula-table entry, can be the singleton `[l]`. The empty
conclusion `[]` means false and adds no negated roots.

The caller supplies canonical clauses: each clause must already equal
`S.sort` of itself and every literal variable must be in the formula table.
The gate rejects noncanonical data rather than silently changing the exact
premises or conclusion. If the CPC surface representation needs a single
formula literal instead of a clause, the adapter must implement and justify
that representation faithfully.

`root_claims` must have the exact length, order, and literal sequences of
`local_roots cs c`. Slot numbers may be chosen freely within `capacity`, but
must be distinct. Roots are loaded into a fresh `S.make capacity`; no existing
`S.t`, global clause lookup, callback, external assumptions, or arbitrary
semantic proof enters the API. Initialization uses `S.set_clause` only after
the canonical check, so it preserves those exact literal sequences.

Each command must read only live, bounded local slots, write a fresh bounded
local slot, use bounded explicit formula literals, and produce exactly
`expected`. All commands execute, even commands after an already obtained
conflict. A failed or unsupported command fails the entire gate. The final
`conflict` must be a live bounded slot containing exactly `[]`.

`load_roots_binding`, `gate_binding`, `available_spec`, `fresh_spec`, and
`execute_binding` expose these executable boundary checks for integration.
`load_roots_valid`, `execute_valid`, and `run_valid` establish semantic state
preservation. Assuming the conclusion false makes precisely the additional
negated roots valid (`local_roots_valid`). Acceptance then contradicts the
existing clause interpretation of the empty clause, proving `gate_correct`.

## Supported semantic operations and conservative rejection

`decode` translates the following existing `Checker_Ext.step` shapes into
`Euf_Checker.step`, with their complete clause-read footprint:

| Operation | Local reads |
| --- | --- |
| `Res` | Exactly the two IDs in its resolution array |
| `Weaken`, `ImmFlatten` | Their source clause ID |
| `CFalse` | None |
| `BuildDef`, `BuildDef2`, `BuildProj` | None |
| `ImmBuildDef`, `ImmBuildDef2`, `ImmBuildProj` | Their source clause ID |
| `EqTr`, `EqCgr`, `EqCgrP` | None (produce valid implication clauses) |
| `LiaMicromega`, `LiaDiseq` | None |
| `SplArith`, `SplDistinctElim` | Their source clause ID |

This is a switch over existing SMTCoq semantic checker operations, not a CPC
rule evaluator. A witness can compose several operations to establish one
CPC result that is not directly produced by any single small checker.

The output of every command except the dedicated `CTrue` operation must differ
from `C._true`. Existing small-checker failures return that clause. `CTrue`
is separately recognized and must produce exactly its proved singleton-true
clause. This permits Boolean constant proofs without accepting a failed EUF,
CNF or resolution operation as a tautology. Resolution arrays must have length two so every
individual resolution link is exposed to this check. Longer chains must use
separate fresh binary operations. Unsupported shapes, including all
BV operations and array operations, return `None`. `Checker_Ext.step` contains
neither proof-carrying `Hole` nor `ForallInst`; these cannot be constructed as
commands. There is no witness-cut field.

## Concrete example and tests

In `EunoiaLocalTests.v`, `trans_witness` certifies the unit result `x=z` from
unit premises `x=y` and `y=z`. Its roots are `[x=y]`, `[y=z]`, and `[not(x=z)]`.
An `EqTr` operation produces the existing EUF implication clause
`[not(x=y);not(y=z);x=z]`; three local binary resolutions derive `[]`.
The unit consequence is therefore accepted despite not being the EUF
checker's immediate output clause.

The 44 kernel-computed regression examples cover:

- EUF transitivity and function congruence;
- Boolean equality introduction using CNF and resolution;
- Boolean predicate congruence yielding the unit formula
  `P(z,x) iff P(z,y)` from `x=y`, using both congruence directions and CNF;
- LIA implication composed with resolution;
- clause and formula disjunctions, empty conclusions, and empty root conflicts;
- changed endpoints, changed EUF certificates, changed intermediate clauses,
  altered/reordered/missing/extra roots, and disjunctive-root strengthening;
- duplicate roots and outputs, forward/uninitialized/global/OOB reads, OOB
  outputs and conflict slots, malformed literals, noncanonical clauses,
  unsupported operations after conflict, invalid tables, and EUF/CNF/resolution
  fallback rejection.

These are hand-built local witnesses. No automatic witness producer or CPC
adapter integration is included. The tests check table structure; semantic
use of their accepted witnesses still requires the theorem's `Atom.wt` proof.

## Build, audit, and integration status

The existing isolated `theories/checker/eunoia/dune` stanza discovers these
modules automatically; no dune, tactic, core, generator, or adapter file was
changed. Reproduce targeted verification with:

```sh
/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2 theories/checker/eunoia/EunoiaLocalTests.vo
```

Every lemma added to `EunoiaLocal.v` has a `Print Assumptions` command. Its
soundness theorem inherits Uint63 primitives/specifications and the existing
`ProofIrrelevance.proof_irrelevance` dependency of
`Euf_Checker.step_checker_correct`; this module declares no axioms or parameters
and has no proof holes. Compile the source afresh to emit the audit. An additional
temporary compatibility theorem was compiled against a read-only copy of the
coordinator's `EunoiaChecker.v`, proving the exact core gate contract.

Verification commands, logs, exit codes, branch, and local commit IDs are in
the implementation job's final report. Temporary compatibility sources and the
complete audit are under `/tmp/eunoia-local-interop/` and
`/tmp/eunoia-local-assumptions.log` on this machine.

Remaining coordinator work: connect per-step witness production to faithfully
bound generated results; instantiate the core gate; preserve full CPC trace
coverage and exact authoritative root binding; establish `Atom.wt` for imported
tables; and run integrated CPC fixtures. Coverage and performance of generated
CPC rules have not been established by these local tests.
