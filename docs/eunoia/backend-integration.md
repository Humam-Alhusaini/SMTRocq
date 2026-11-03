# OCaml Eunoia backend integration

This child supplies a compiled OCaml solver/reification/proof-builder pipeline.
It does not claim an operational general cvc5 tactic or complete QF_UF/QF_LIA
coverage. The current generated rule fragment rejects ordinary cvc5 `evaluate`
steps; no rule or scope is skipped to obtain a theorem.

## Concrete coordinator API

The isolated library is `eunoia_backend` (`rocq-smtcoq.eunoia_backend`), with its
own `src/eunoia_backend/dune`. No common, LFSC, shared dune, grammar, or tactic
source was changed by this child.

Register this checked entry point after integrating the witness producer:

```ocaml
module B = Eunoia_backend.EunoiaBackend
module C = Eunoia_backend.EunoiaRocq
let witness ~atoms ~forms ~premises ~conclusion =
  match Eunoia_witness.Search.produce ~atoms ~forms ~premises ~conclusion () with
  | Error e -> Error (Eunoia_witness.Search.string_of_failure e)
  | Ok candidate ->
      Ok (Eunoia_witness.Certificate.to_coq
        ~local:(fun s -> C.global
          ("SMTCoq.checker.eunoia.EunoiaLocal.EunoiaLocal." ^ s))
        ~step:(fun s -> C.global
          ("SMTCoq.checker.MainChecker.Checker_Ext." ^ s)) candidate)
let eunoia_bool () = B.tactic ~witness ()
```

The callback type is deliberately independent of an unmerged library:

```ocaml
type witness_producer =
  atoms:SmtAtom.Atom.reify_tbl -> forms:SmtAtom.Form.reify ->
  premises:SmtAtom.Form.t list list -> conclusion:SmtAtom.Form.t list ->
  (RocqInterface.constr, string) result
```

The result must construct `EunoiaLocal.witness`. The backend never treats a
successful callback as proof. Every candidate, including candidates for unused
CPC steps, goes into a single adapter trace checked with `EunoiaLocal.gate`.
The ordinary tactic targets `EunoiaTactic.checker_b_correct` for requested
Boolean results and `checker_eq_correct` for Boolean equality. Those wrappers
fix both the local semantic gate and authoritative negated-goal roots inside
Rocq, and discharge their own typing/gate preconditions. The supplied-lemma
path uses `EunoiaTactic.checker_correct` and constructs the root-validity proof
from the current goal and the supplied proof terms. It does not use the
adapter's single-step `checked_checker` wrapper.

Coordinator changes still required:

1. Add `eunoia_backend` and `eunoia_witness` to the plugin library dependencies
   in `src/dune`, and register the wrapper above in `src/g_smtcoq.mlg`.
2. The committed local gate and goal wrappers have been merged here. Require
   `EunoiaTactic`, `EunoiaAdapter`, `EunoiaLocal`, `EoSyntax`, and `CpcGenerated` before calling
   the plugin. Constant lookup fails with the missing fully qualified name.
3. Export a user tactic in `theories/tactics/Tactics.v` using existing
   preprocessing (`preprocess1`, `prop2boolImp`, etc.) to obtain Boolean
   equality/is_true and CompDec instances. The OCaml entry has optional
   `~preprocess` and `~lemmas` hooks; its default preprocessing is `intros`.
   Lemmas must prove a quantifier-free Boolean fact (`is_true f` or `f=true`);
   supplied proof terms are reused in the kernel-checked root-validity proof.
   Missing CompDec cuts are rejected explicitly, never turned into assumptions.
4. Expand the actual signature generator before expecting ordinary live cvc5
   proofs to work; `derive` is the only production rule evaluator. Extend the
   syntactic adapter/reifier agreement explicitly where needed.
5. Scope discharge must use the proved scoped checker. This implementation
   rejects `assume-push`, `step-pop`, and directives. It does not drop scopes.

`B.build_refutation` is also available for callers already holding the four
reification tables and ordered root formulas. It returns a proof of
`~ Forall (C.valid valuation) (map singleton roots)`.
`build_refutation_from_cpc` and `tactic_from_cpc` replay a strict parsed proof
through the same checker; their roots still come from the caller/current goal.
There is no no-check entry point and no legacy trace/cut fallback.

## Data flow and exact representations

* `EunoiaSolver.run` starts the absolute cvc5 1.4.2 binary from
  `scripts/eunoia/cvc5-1.4.2.json`, never the wrapped PATH's cvc5. Defaults:
  60,000ms solver time, 10,000,000 solver resources, 65s parent wall time,
  and 32MiB per output stream. It uses `fork`/`setsid`/`execv`, private mode-600
  files, bounded stderr diagnostics, kills the private process group, reaps the
  child, and removes files on success/failure/timeout. Options include
  `--dump-proofs --proof-format=cpc --proof-granularity=dsl-rewrite
  --no-proof-allow-trust --proof-check=eager --check-proofs-complete`.
  Exit 0 plus a strictly parsed `unsat (...)` envelope is only untrusted data.
* `export` uses existing `SmtBtype.to_smt` and `Form.to_smt` printers and
  `SmtBtype.to_list` / `Op.to_list` declarations, with deterministic `Tindex_i`
  and `op_i` names. No declarations or interpretations are imported from CPC.
* `EunoiaElaborate` binds every declared name and exact type to that export,
  expands parameterized definitions and parallel lets using parser binding IDs.
  Definitions must use the pinned printer's `@t<digits>` alias namespace; other
  names reject to prevent shadowing signature constants outside the fragment. It
  requires all root assumptions in exact exported order/content. Every
  command is visited, including unused definitions and steps. Premise order and
  multiplicity are retained. Final output must be a generated `false` step.
  Expansion is bounded (default 1,000,000 visits), independent of parser limits.
* The initial root trees are computed with `EunoiaAdapter.encode_clause` from
  the authoritative tables. Result candidates are computed by
  `CpcGenerated.derive fuel (EunoiaAdapter.typeof ...)` using
  `RocqInterface.cbv_vm`. Marshaling preserves binary `Symbol`/`Apply` trees;
  numeric spellings, polarity, operand order and nesting are retained.
* Result formulas go through existing `Smtlib2_genConstr.make_root`; it may
  canonicalize syntax. This is an untrusted candidate construction only. The
  final adapter re-encodes each exact result clause and every premise clause,
  reruns `derive`, and compares exact syntax; any mismatch rejects. `false`
  results explicitly use the empty clause; other results use singleton clauses.
  Maps are cleared on return. Witness search may intern auxiliary equalities;
  the final authoritative table snapshot is taken after every candidate exists.
* The checker verifies `tables_wf` (including `Atom.wt`), exact roots, root
  claims, all generated rule results, all semantic witnesses, and empty conflict.
  Boolean equality evidence uses VM conversion checked immediately before its
  cast is constructed. The tactic installs the full proof with
  `Tactics.exact_check`, and `Qed`/`rocq check` check the resulting term again.
  A successful solver run, VM decoding, or witness search is never sufficient.

No associative nil insertion/removal, constant simplification, or
commutative/associative rewriting is performed by this backend. In particular,
`(or p q)` does not become `(or p (or q false))`. A signed decimal symbol is
retained as a signed symbol and interned as an existing integer constant;
unary `(- n)` remains an application. Root export spelling and adapter encoding
must agree exactly. Existing reifier equality ordering, numeric normalization,
and double-negation normalization can currently cause rejection. Broader
support requires an explicit, checked representation agreement, not an OCaml
normalization that evades the adapter.

## Verified evidence and reproduction

Environment: private `/home/charles/code/friends/.toolchains/smtrocq-env`,
OCaml 4.14.2 / Rocq 9.3.0. This child used no Ethos or Logos source. The adapter
was integrated by merging committed `smtrocq/cvc5-eunoia` at `1ebadf6`, containing
adapter commits `85a5694` and `af49796`. A second dependency merge included
`EunoiaLocal` (`1263290`, `55a26f3`), concrete `EunoiaTactic` goal wrappers
(`a4866aa`), and the separate scoped core. The generated scoped adapter is
still pending, so scopes remain rejected.

Commands run in the child worktree:

```sh
/home/charles/code/friends/.toolchains/smtrocq-env dune build src/eunoia_backend
/home/charles/code/friends/.toolchains/smtrocq-env dune runtest src/eunoia_backend/tests
/home/charles/code/friends/.toolchains/smtrocq-env dune build theories
python3 src/eunoia_backend/tests/integration/check.py \
  --output /tmp/eunoia-backend-validation
```

All four commands exited **0**, including independent kernel rechecking.
The final driver logs each exact dune,
Rocq compilation, and independent kernel recheck invocation and exit status.
Its source is committed, and its validation log is retained at
`/tmp/eunoia-backend-validation.log` (the final rerun is
`/tmp/eunoia-backend-validation-final.log`). Dependencies are copied only to the
explicit `/tmp` validation directory, not committed as snapshots.

The OCaml test invokes the actual private cvc5 and parses its CPC output. It
rejects SAT, malformed solver input, oversized output, and a parent wall timeout,
and verifies temporary-file cleanup. Elaboration tests cover exact ordered
premises, changed claimed conclusions, changed/missing declarations, changed
roots, unused unknown-rule steps, unused unknown-symbol definitions, signature-name redefinitions, unsupported
scopes, parameterized definitions, parallel lets, and exhausted expansion budget.
The test-only derive callback in these syntax tests is not used by the backend.

The Rocq harness constructs a checked `p=p` proof from a small CPC replay using
the real generated `refl` and `contra` rules. Its local witnesses use existing
CNF definition and resolution operations. It exercises the concrete Boolean-true, Boolean-false and equivalence
correctness lemmas, and also reuses a supplied hypothesis proof as an
additional bound root. Negative tactics reject an appended unused
`trust` step, an invalid local witness, and an invalid witness attached to an
unused **supported** `refl` step. The initial live solver tactic is tested with
`Fail`, because its CPC includes unsupported generated rules. That failure is
an explicit coverage deficit, not successful end-to-end cvc5 evidence.

All four replay example lemmas run `Print Assumptions`. No new soundness lemma,
axiom, or parameter is introduced in production. The replay proofs inherit the
existing SMTCoq Uint63/PArray primitive specifications and existing proof
irrelevance through the adapter and semantic gate; they are not advertised as
axiom-free. The committed harness also independently runs `rocq check -silent`
on its resulting proof module without dependency-admission options.

An earlier isolated successful replay also used the witness producer's early
`Search.produce` / `Certificate.to_coq` API directly, copied for testing only.
That owner's HEAD was `6ce3cf12dcecbdb14f1af1f3754e49a7fe467e82` with the new
witness sources uncommitted; hashes are retained at
`/tmp/eunoia-backend-dependencies.sha256` and copies at
`/tmp/eunoia-backend-witness-snapshot/`. The committed harness instead supplies
small test-only candidates so it builds independently of that unmerged library.
The first validation used local-gate owner HEAD
`55a26f30da9e91d06b1dd801f1f881a1f57df574` as a read-only external dependency.
The final reproducible validation uses the merged committed source directly.

Still incomplete: shared tactic/plugin wiring; integration of the production
witness library; proved scopes; generated coverage of actual
cvc5 traces; exact representation agreements; successful general live solver
proofs; representative complete UF/LIA tactic benchmarks. No completion of the
cvc5/Eunoia port is claimed.
