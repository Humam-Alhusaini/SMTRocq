# SMTCoq architecture for a generated Eunoia backend

Research snapshot: 2026-11-03, source commit
`2e1c1a7e1c1c8c24dccef330675789371a13ee1d`, child branch
`t3/document-smtcoq-architecture` (initially named `t3/8cba40a9`).
This report follows [implementation-plan.md](implementation-plan.md). It describes
existing interfaces and a proposed integration; it does not establish CPC rule
coverage or an operational Eunoia backend. Only this report changes source files.

## 1. Reuse boundary

Keep SMTCoq's interpretation tables, literals, clauses, state, and small checkers.
Generate CPC syntax, executable rules, and side conditions from the actual
signature and its transitive includes/helper programs. Then check the semantic
consequence of **each** generated result in the existing interpretation. The
generator's executable rule relation and the semantic consequence check have
different obligations; neither substitutes for the other.

The current proof-producing route is:

```text
Rocq goal / SMT-LIB assertions
  -> SmtBtype / SmtAtom / SmtForm reification tables
  -> solver-specific parser and SmtCertif/SmtTrace certificate
  -> Rocq Euf_Checker.certif
  -> Euf_Checker.checker[_b|_eq] computes true
  -> checker[_b|_eq]_correct applied to a checked equality proof
  -> Rocq proof of the original goal (with preprocessing/cut proofs)
```

The OCaml parser, solver, certificate transformations, and arithmetic witness
search supply candidate data. Soundness comes from the Rocq checker theorem and
its successful evaluation, with the exact reified goal and interpretation tables
as theorem arguments. A solver's `unsat` output is not such an argument.

## 2. Existing semantics and state

Paths below are relative to the repository root; line numbers refer to the
snapshot above. Physical `small-checkers/` maps to logical `small_checker`.

| File and location | Symbols | Contract relevant to Eunoia |
| --- | --- | --- |
| `theories/utils/PArray.v:74` | `array`, `make`, `get`, `set`, `default`, `length` | Software arrays represented by an AVL finite map, default, and `Uint63.int` length. Out-of-range reads return the default; writes do not grow an array. These are not `Stdlib.PArray` primitive arrays. |
| `theories/checker/fol/State.v:26` | `Valuation.t`, `Valuation.wf`, `Var` | Boolean valuation of integer-indexed variables; indices 0 and 1 mean true and false. |
| `State.v:53` | `Lit.is_pos`, `blit`, `lit`, `neg`, `nlit`, `interp`, `interp_neg` | Literals are `Uint63.int`; variable index is `l >> 1`, positive literals are even, negation is xor with 1. |
| `State.v:245` | `C.t`, `C.interp`, `C.valid`, `C._true`, `C.is_false`, `C.is_false_correct` | Clause = list of literals; interpretation = disjunction (`existsb`). Empty clause is false; `[Lit._true]` is the safe default. |
| `State.v:440` | `S.t`, `S.make`, `S.get`, `S.valid`, `S.valid_make`, `S.valid_get` | State = array of clauses; validity means **every** lookup is true. Initial/default clauses are tautologies. |
| `State.v:616` | `S.set_clause`, `S.valid_set_clause`, `S.sort`, `S.sort_correct` | Stores a sorted clause, with a validity-preservation theorem. Current `set_clause` uses `sort`, not `sort_uniq`; do not assume duplicate removal. |
| `State.v:655` | `S.set_resolve`, `S.valid_set_resolve`, `C.resolve_correct` | Resolves an array of clause IDs. Empty resolution is a no-op; missing/out-of-range premises get the state's default. |
| `State.v:683` | `S.subclause`, `S.check_weaken`, `S.set_weaken`, `S.valid_set_weaken` | Verified weakening; failure produces the tautology. |
| `theories/utils/CompDec.v:124,163` | `CompDec`, `typ_compdec`, `te_carrier`, `te_compdec` | Interpretation of an uninterpreted sort carries actual equality, order/comparison, and inhabitance evidence. It is not an arbitrary unproved equality oracle. |
| `theories/checker/fol/Terms.v:33` | `Form.form`, `Form.interp_aux`, `t_interp`, `interp_state_var` | Formula DAG: atoms, true/false, repeated double negation, n-ary and/or/implication, xor, iff, ite, bit-blasting predicate. |
| `Terms.v:114,230` | `Form.lt_form`, `wf`, `check_form`, `check_form_correct`, `wf_interp_form` | Children precede parents. Boolean checks establish the default `Ftrue`, reserved true/false entries, acyclicity, and `Valuation.wf`. |
| `Terms.v:265` | `Typ.type`, `Typ.interp`, `Typ.i_eqb`, `Typ.i_eqb_spec` | Existing sorts include `TZ`, `Tbool`, `Tpositive`, `Tindex`, bitvectors, functional arrays. Reuse their interpretation rather than adding an SMT-LIB semantics. |
| `Terms.v:716,1004` | `Atom.atom`, `Atom.val`, `bval`, `tval`, `interp_aux` | Atom DAG with typed operators and `Aapp` for uninterpreted functions; dependent values package their sort and denotation. |
| `Terms.v:2233,2555` | `Atom.lt_atom`, `wf`, `get_type`, `wt`, `check_aux` | Structural acyclicity and Boolean type checking are separate obligations. `wt` checks all atom nodes against their interpreted types. |
| `Terms.v:2563,2580` | `Atom.interp_hatom`, `interp_form_hatom`, `interp_form_hatom_bv`, `check_atom`, `check_atom_correct` | Shared denotation of atoms. `check_atom` establishes acyclicity/default `Acop CO_xH`; it does not by itself establish `Atom.wt`. |

For all semantic bridges use the same valuation:

```coq
Form.interp_state_var
  (Atom.interp_form_hatom t_i t_func t_atom)
  (Atom.interp_form_hatom_bv t_i t_func t_atom) t_form
```

Do not conflate an atom ID, formula ID, encoded literal, and clause ID: their
machine representation overlaps, but their meaning and bounds differ. The new
front end must also reject integer overflow before converting IDs to `Uint63`.

## 3. Checker composition and tactic correctness

`theories/checker/MainChecker.v:31` defines the generic trace framework:

* `_trace_ step` is **`list step * step`**, not the old nested array format still
  visible in comments. `_checker_` folds `check_step` over `fst t` and tests
  `is_false (S.get final confl)`. The second component is a serialization default
  and is **not executed**.
* `_checker__correct` needs `valid_check_step` (each transition preserves
  `S.valid rho`) and `is_false_correct` (the final clause cannot be true).
  It concludes that a successful refutation implies the initial state was not
  valid. This is the reusable composition theorem, not a theorem about CPC.
* `Sat_Checker` supplies resolution; `Cnf_Checker` adds verified Boolean/CNF
  rules. `Euf_Checker` adds EUF, arithmetic, arrays, bitvectors, and proof-carrying
  extensions. The name `Euf_Checker` therefore understates its scope.

`Euf_Checker.step` (`MainChecker.v:336`) and `step_checker` (`:389`) dispatch
to small checkers; `step_checker_correct` (`:435`) proves state preservation
assuming `Form.check_form`, `Atom.check_atom`, and `Atom.wt`.
`euf_checker_correct` (`:499`) instantiates `_checker__correct`.
`Certif` (`:512`) stores state capacity, the trace, and final conflict ID.

`Euf_Checker.checker` (`:541`) tests all three table conditions and refutes
the state constructed by `add_roots`. `checker_correct` (`:725`) proves
`checker d used_roots c = true -> ~ valid t_func t_atom t_form d`, where `valid`
is the conjunction of interpretations of input literals.

The goal-specific wrappers are significant, not cosmetic:

| Symbol (`MainChecker.v`) | What is checked | What correctness supplies |
| --- | --- | --- |
| `Euf_Checker.checker_b` / `checker_b_correct` (`:732`, `:737`) | If desired result `b` is true, seed roots with `Lit.neg l`; otherwise with `l`. Existing implementation repeats that literal in `PArray.make nclauses l` and uses `used_roots=None`. | `Lit.interp rho l = b`. This does not require a trusted correspondence between solver assertion names and the goal: the theorem itself fixes the roots. |
| `Euf_Checker.checker_eq` / `checker_eq_correct` (`:744`, `:753`) | Require negative literal `l`; require its formula entry to be exactly `Fiff l1 l2`, checking both child IDs; refute repeated roots `l`. | Equality of the **Boolean interpretations** of `l1` and `l2`. This is not directly Leibniz equality of arbitrary SMT terms. |

`SmtCommands.core_tactic` reifies a Boolean equality goal `a=b`; when `b` is a
Boolean constant it uses `build_body` and `checker_b_correct`. Otherwise
`build_body_eq` constructs a negative `Fiff` and applies `checker_eq_correct`.
Propositional preprocessing and interpreted Boolean term equality connect these
results to user-facing propositions/term equalities.

`Checker_Ext` (`MainChecker.v:896`) is a separate extractable checker without
proof-carrying `Hole`/`ForallInst` cases. Its `checker_ext_correct` quantifies over
`t_i,t_func` and **requires** `Atom.wt` as a hypothesis; its Boolean
`checker_ext` checks form/atom structure but does not itself check typing. It is
not an unconditional replacement for the tactic checker.

## 4. Reusing EUF, Boolean reasoning, and LIA

### EUF and Boolean rules

`theories/checker/small-checkers/euf/EUF.v` exports:

* `check_trans` (`:77`), proved by `valid_check_trans` (`:336`). It constructs
  an equality-chain implication clause, orienting equality endpoints as needed.
  Empty premise equality lists check reflexivity.
* `check_congr` (`:98`), proved by `valid_check_congr` (`:397`). It checks
  congruence for matching atom operators/functions. Its equality witnesses are
  `list (option _lit)`; `None` requires identical argument IDs, `Some l` supplies
  a checked equality link (either orientation).
* `check_congr_pred` (`:114`), proved by `valid_check_congr_pred` (`:469`), supplies
  predicate congruence clauses. The concrete interpretation/type hypotheses
  appear in the `Proof` subsection starting at `:139`.

These return universally valid **clauses**, not an unchecked equality result.
For a CPC step using established equalities, generate the implication clause and
resolve its antecedents against the exact premise clauses. Reflexivity/symmetry/
transitivity and ordinary function/predicate congruence can reuse these checkers.
The bridge must check the returned clause against the claimed CPC conclusion;
an equality list and conclusion with unrelated IDs is not a semantic bridge.

`small-checkers/cnf/CNF.v` supplies `check_True`, `check_False`, `check_BuildDef`,
`check_BuildDef2`, `check_BuildProj` and their immediate-premise variants, with
`valid_check_*` theorems. They cover Boolean connective clauses/projections and
can be combined with `S.set_resolve`. `spl/Syntactic.v:396` provides
`check_flatten` / `valid_check_flatten` (`:581`); `spl/Operators.v` provides
distinct elimination / `valid_check_distinct_elim`. Require their actual shape
checks; normalization in OCaml alone is not proof evidence.

CPC congruence is broader than equality of atom `Aapp`s: Boolean connectives
live in `Form`, not necessarily `Atom`. Boolean equality/negation/ite rewrites
need CNF-derived equivalences or new proved bridges. Do not equate the CPC name
`cong` with `EqCgr` without inspecting the generated result's syntax and sorts.

### Integer arithmetic

`theories/checker/small-checkers/lia/LIA.v:22` translates existing atom/form
syntax to Micromega formulas: `build_positive`, `build_z`, `build_pexpr`,
`build_formula`, `build_hform`, `build_nlit`, and `build_clause`. Translation can
fail (`option`); the checker handles that conservatively.

* `check_micromega cl c` (`:353`) runs `ZTautoChecker` on the translated
  clause using `list ZMicromega.ZArithProof`. It returns `cl` on success and
  `C._true` on failure. `valid_check_micromega` (`:1528`) uses
  `ZTautoChecker_sound` and the existing translation correctness proofs.
* `check_diseq` (`:361`) / `valid_check_diseq` (`:1547`) recognize the specific
  three-way total-order formula `a=b or not(a<=b) or not(b<=a)`; this is not a
  general arithmetic decision procedure.
* `spl/Arithmetic.v:34` supplies `check_spl_arith` /
  `valid_check_spl_arith` (`:68`) to check an arithmetic consequence of an
  existing clause with Micromega witnesses.
* `src/lia/lia.mli:15` exposes
  `Lia.build_lia_certif : SmtAtom.Form.t list -> zArithProof list option`.
  The implementation (`lia.ml:156,171`) calls Micromega's OCaml witness search;
  the resulting witnesses are data subsequently checked in Rocq.

For a CPC arithmetic step, check the exact implication from its translated
premises to its translated conclusion. Prefer direct conversion of the CPC
arithmetic witness when available. Micromega witness search for that individual
implication is also a possible semantic certificate gate, provided Rocq checks
the witness and exact endpoints. Re-solving the overall problem and ignoring
the CPC trace would violate the implementation contract. Existing polynomial
syntax and a certificate search API do not establish coverage of cvc5's integer
rounding, division, normalization, or cutting rules; inventory and prove those
bridges separately. Initial support remains QF_LIA.

## 5. Assumption and premise binding

### File imports

`Smtlib2_genConstr.import_smtlib2` (`src/common/smtlib2_genConstr.ml:434`)
returns assertions in source order. It populates `SmtBtype`, `Op`, `Atom`, and
`Form` tables. `declare_sort_from_name` and `declare_fun_from_name` create Rocq
sort/function context entries; sort `CompDec` evidence is also required.
`declare_commands` handles sort/function declarations and assertions but has a
catch-all ignoring other commands. It is not a complete fail-closed SMT-LIB
validator: Eunoia must explicitly reject unsupported commands/scopes/logics
before relying on it, and check signature arities/sorts against the input.

`SmtCommands.compute_roots` (`src/common/smtCommands.ml:77`) matches each used
singleton certificate root to an input formula using `Form.equal` and builds
indices into the input root array. `SmtTrace.order_roots` (`smtTrace.ml:153`)
orders solver roots; see `Verit.import_trace` (`src/verit/verit.ml:61`) for the
use of `Syntax.init_index`, `qf_to_add`, and a verified `ImmFlatten` bridge.

At the Rocq boundary, `Euf_Checker.add_roots` (`MainChecker.v:515`) either loads
all input singleton clauses or an indexed subset. An out-of-bounds used-root
index loads `C._true`, never a solver-provided assertion. `add_roots_correct`
proves this preserves validity when all original assertions hold. Refuting a
subset still refutes their conjunction, so root omission is sound for the old
theorem, but this is weaker than the new requirement to validate every CPC
assumption and step. The Eunoia root gate should reject changed, extra, missing,
or out-of-range bindings, rather than rely on a benign default.

### Tactic hypotheses and proof-carrying extensions

`SmtCommands.core_tactic` (`:737`) receives actual Rocq lemma terms/types,
reifies them, and records their formulas in `lem_tbl`. `find_lemma` (`:769`)
re-hashes the solver formula into the quantified reification tables and finds
the corresponding **proof term**; mismatch fails. `make_proof` (`:670`) creates
the distinguished negated-goal root. The tactic's `checker_b`/`checker_eq` call
binds that goal directly as described above.

`Euf_Checker.Hole` carries a proof of `interp_conseq_uf rho prem concl`.
`ForallInst` carries a proposition, a proof of that proposition, and a proof
that it entails the conclusion. Neither is a proof hole in the Rocq theorem.
`small-checkers/spl/Assumptions.v` defines `interp_uf`, `interp_conseq_uf`,
`check_hole` (`:70`), `valid_check_hole` (`:128`), and
`valid_check_forall_inst` (`:108`). `check_hole` uses length-sensitive
`forallb2` comparisons to bind premise IDs to their declared clauses, comparing
state clauses against `S.sort_uniq` of the supplied premises. This detail
matters because the current `S.set_clause` uses `sort` and can retain duplicates.

The OCaml `Hole` constructor does **not** already contain that proof:
`SmtTrace.to_coq` (`src/common/smtTrace.ml:466`) emits a named cut for it.
Similarly `Forall_inst`/`Qf_lemma` emit application-proof cuts. Tactic code
(`smtCommands.ml:806`) turns cuts, including `SmtBtype.get_cuts`, into proof
obligations. In contrast, `parse_certif`, `theorem`, and `checker` file commands
declare certificate cuts as new variables and print an assumption warning.
The legacy LFSC converter can introduce `Hole` for unsupported/trusted rules
(`src/lfsc/converter.ml:1184`). Reusing those fallback paths would violate this
port's constraints. The initial Eunoia path should reject all such fallback
cases and never call `declare_new_variable` to discharge semantic obligations.

## 6. OCaml and tactic integration points

| Interface | Existing API / consequence |
| --- | --- |
| `src/common/smtBtype.mli` | `create`, `of_coq`, `of_coq_compdec`, `interp_tbl` / `make_t_i`, `get_cuts`. Share the sort table; use actual `CompDec` instances. |
| `src/common/smtAtom.mli` | `Op.create`, `Op.declare`, `Op.interp_tbl` / `make_t_func`; `Atom.create`, `get`, `of_coq`, `hash_hatom`, `interp_tbl`, `to_coq`, `mk_eq_sym`, integer constructors. The exported `Form` module is the atom-instantiated formula reifier. |
| `src/common/smtForm.mli` | `FORM.create`, `get`, `of_coq`, `hash_hform`, `flatten`, `right_assoc`, `to_lit`, `to_coq`, `interp_tbl`, `interp_to_coq`. `interp_tbl` supplies table terms; `interp_to_coq` helps relate literal meaning to concrete Rocq expressions. |
| `src/common/smtCertif.mli` | Mutable graph of `clause` records, `Root`, `Same`, `Res`, `Other`; legacy rule payloads include `EqTr`, `EqCgr`, `LiaMicromega`. This is an old-checker certificate language, not CPC syntax. |
| `src/common/smtTrace.mli` | `mkRootV`, `mkRes`, `mkOther`, `link`, `repr`, `order_roots`, `select`, `occur`, `alloc`, `naive_alloc`, `build_certif`, `to_coq`. `select` prunes unused nodes; `alloc` reuses slots. Disable pruning for CPC validation and initially use append-only IDs; retain all original step records. |
| `SmtTrace.to_coq` | Takes a formula encoder, consequence-type builder, a large tuple of old checker constructor constants, a conflict node, and optional lemma lookup; returns trace term, last root, cuts. It cannot encode arbitrary generated Eunoia steps merely by changing solver callbacks. |
| `src/common/coqTerms.ml:302,396` | `euf_checker_prefix`, `ceuf_checker_*`, `ceuf_checker_certif_ops` resolve `Register` names from `MainChecker.v:800`. New checker/constructor constants need their own registry namespace. |
| `src/common/rocqInterface.ml:107` | `mkTrace` emits the list/default pair. `CoqTerms.mkArray` (`:451`) builds software arrays; the last OCaml array element is the default, not a logical data entry. |
| `src/common/smtCommands.mli` | File commands consume `(rt,ro,ra,rf,roots,max_id,confl)`. `tactic` takes an integer mode and solver callback returning `(max_id,confl)`, logic, six reification tables, VM proof builder, and Rocq lemma lists. |
| `src/common/smtCommands.ml:22,552,609` | Checker constants and trace construction are fixed to `Euf_Checker`; `build_body` and `build_body_eq` create let-bound tables/certificate and apply correctness. Refactor/parameterize both checker constants **and encoding**, or provide a sibling builder for generated certificates. |
| `src/verit/verit.ml:269`, `src/lfsc/lfsc.ml:591` | Examples of solver-specific table setup and invocation of `SmtCommands.tactic`. `Lfsc.import_trace` currently calls `select`, `occur`, `alloc` after conversion. |
| `src/g_smtcoq.mlg` | Registers file commands `Parse_certif_*`, `*_Checker`, `*_Theorem`, and base tactics. A cvc5 abduction tactic already exists; it is not a CPC checker. |
| `theories/tactics/Tactics.v` | Declares the ML plugin; veriT preprocessing uses `Conversion.preprocess1`/`preprocess2` and Trakt; `cvc4_tac` uses the LFSC route. `smt` currently composes veriT/CVC4. Do not silently reroute it before supported coverage is measured. |
| `theories/SMTCoq.v` | Public re-exports of semantics, checker modules, tactics, Trakt database/conversion. |

`CoqTerms.vm_cast_true` (`coqTerms.ml:414`) first checks VM convertibility of the
Boolean checker result with true. `vm_cast_true_no_check` only constructs a VM
cast of reflexivity; the conversion is delayed to proof checking. The legacy
`*_no_check` names therefore mean delayed certificate computation, not permission
to trust a solver. For the new backend use the eager checked path and retain
`Qed`/kernel checking. `USE.md` documents the existing timing distinction.

## 7. Concrete minimal integration plan

This is a proposed interface for coordinator/generator/core agreement, not an
implemented API or a new assumption.

1. **Generated language and rule computation.** Place the signature compiler in
   `tools/eunoia/` and generated Rocq syntax/evaluator in the generator-owned
   subtree under `theories/checker/eunoia/`. Record cvc5/signature versions and
   include hashes. Generated evaluation takes a rule application and its exact
   typed argument/premise results and returns `option result`. Check any supplied
   conclusion against that result. Unknown rules/programs, bad side conditions,
   malformed arity/sorts, nontermination/fuel exhaustion all reject. A hand-coded
   CPC rule switch, even if semantically proved, does not meet generation scope.

2. **One translation boundary.** Translate supported CPC terms into the existing
   atom/form tables, with an explicit typed term-to-ID map. Give the supported
   translation a checked structural correspondence and prove its Boolean/clause
   interpretation through `Terms`; do not introduce an independent evaluator
   for SMT-LIB meaning. A root table built independently from the original goal
   or file must match translated CPC assumptions, including symbol identity,
   sort/arity, polarity, and structure. Initially require an exact ordered root
   list and reject unsupported scopes/assumption discharge. Definitional aliases
   need explicit checked expansion, not fresh unrelated SMT variables.

3. **Checked step over `S.t`.** Each record retains CPC step ID, rule application,
   exact premise IDs, generated result, translated claimed clause, and semantic
   witness. Return `option S.t`, with a proved obligation: successful transition
   from `S.valid rho s` preserves `S.valid rho`. Keep an allocated/established-ID
   map separately from `S.t`: defaults in `S` do not distinguish a missing clause
   from an established tautology. Reject forward/missing references, duplicate
   IDs, overflow, out-of-range writes, and scope violations before transition.

4. **Minimal semantic witness gate.** One feasible first implementation is a
   short **local** certificate in the existing verified small-checker language.
   Construct a fresh local `S.make`; load only the exact translated premise
   clauses, then execute allowed EUF/CNF/LIA/resolution operations. Use
   `Euf_Checker.step_checker_correct` to prove preservation (exclude `Hole` and
   `ForallInst` operationally), or call the corresponding small theorems
   directly. Require its final clause to equal the claimed CPC clause after
   an explicitly proved sorting/normalization, checking lengths and literals.
   Thus a small-checker failure returning `C._true` cannot stand in for a
   non-tautological claimed result. A tautological conclusion can pass only if
   the generated CPC application itself is valid. Fresh local state prevents
   semantic witnesses from depending on unrelated global clauses. Direct proved
   bridges can replace these local certificates as coverage improves.

5. **Whole trace and refutation.** Fold an option-valued checked transition over
   **all original CPC steps**, propagating failure. Do not use old `select` or
   silently drop alias/rewrite steps. Prove successful-fold state preservation,
   then refutation using `C.is_false_correct` and root validity. `_checker__correct`
   can help if an explicit failure flag/wrapper ensures that any failed step
   rejects the whole certificate; a mere identity transition on failure is
   insufficient. Require the designated final generated result to translate
   to false (empty clause or a separately verified false singleton conversion).
   The old unused default trace component is not an acceptable place for a CPC
   step. Every original record must be visited by the checked evaluator.

6. **Public correctness and plugin.** Prove Eunoia analogues of `checker_correct`,
   `checker_b_correct`, and `checker_eq_correct` with the same interpretation and
   explicit goal/root binding. A generated trace is a different certificate;
   the existing wrapper theorems do not apply to it automatically. Implement a
   sibling `src/eunoia/` parser/encoder/solver wrapper, and parameterize or share
   the reusable goal reification/proof-building code. Start with file checking
   and a dedicated eager checked tactic before changing `smt` dispatch. Require
   no generated certificate cuts and no new top-level semantic assumptions.

The actual `/tmp/smtrocq-uf4.cpc` is a useful first integration target: one
top-level conjunction assumption, definitional aliases, then 15 steps using
`evaluate`, `eq-refl`, `cong`, `trans`, `and_elim`, and `eq_resolve`. Most steps
omit an explicit conclusion; the generated evaluator must compute it. The early
`evaluate`/reflexivity/congruence/transitivity chain must also be checked even if
a separately reconstructed smaller refutation could avoid it. This observation
is about syntax in the fixture, not a claim these rule bridges are implemented.

### Coordinator-owned build/tactic edits required later

No shared dune/tactic files are changed here. A possible isolated new theory
stanza is `SMTCoq.checker.eunoia` depending on `Stdlib`, existing
`SMTCoq.checker`/`SMTCoq.checker.fol`, and the generated syntax theory. Separate
generic state infrastructure from generated code if necessary to avoid cycles;
the generator and core owners must settle their exact module names together.

The coordinator will need to wire `src/eunoia/dune` and its library into
`src/dune`, add registry lookups/proof builders as appropriate in common code,
register dedicated commands in `src/g_smtcoq.mlg`, and update the theory/tactic
dependencies and exports in `theories/dune`, `theories/tactics/dune`,
`theories/tactics/Tactics.v`, and `theories/SMTCoq.v`. Add new test stanzas without
editing generated `unit-tests/files/dune.inc` by hand. Preserve eager checking,
actual hypothesis proof terms, and existing solver behavior during integration.

## 8. Tests and proof assumptions

`unit-tests/dune` builds `abduce_tactics.v`, `lfsc_tactics.v`,
`verit_tactics.v`, and `zchaff_tactics.v`; its `runtest` aliases recursive `all`.
`debug_manually.v` and `large1.v` are outside that explicit module list.
`unit-tests/files/generate_dune_rules.sh` creates/promotes `dune.inc`, generating
solver output plus vernacular checking/import/theorem tests from `.smt2`/`.cnf`
fixtures. It explicitly skips numerous LFSC fixtures, including all `lia*` and
`uf4`, and some veriT fixtures. Existing test success cannot demonstrate CPC or
complete QF_UF/QF_LIA coverage. `examples/dune` also has a `runtest` alias;
`benchmarks/` has separate fixture generation.

Add deterministic retained CPC fixtures with generated-evaluator, translated
semantic-witness, whole-trace, and dedicated tactic tests. Include mutations of
rule/argument/conclusion, missing/forward/duplicate premise IDs, unknown
**unused** rules, changed/extra/missing roots, alias/sort changes, invalid local
arithmetic witnesses, and an unsupported scope. Check rejection as a Boolean
result or `Fail` command in a closed test, without unfinished proof placeholders.
Retain positive examples for function/predicate congruence, reversed equality,
Boolean rewriting, and integer arithmetic. Separate solver regeneration from
deterministic certificate checks and checked-tactic timing from solver-only time.

### Observed assumption baseline

Rocq 9.3.0 / OCaml 4.14.2 / dune 3.21.1, through the required private wrapper.
`Print Assumptions` was run on existing lemmas; no new soundness lemma was added.
Counts below count declaration names printed by Rocq, including primitives.

| Audited declarations | Result |
| --- | --- |
| `_checker__correct` | 12 `PrimInt63` / `Uint63Axioms` entries |
| `Sat_Checker.checker_correct`, `Cnf_Checker.checker_b_correct` | 51 `PrimInt63` / `Uint63Axioms` entries each |
| `Euf_Checker.step_checker_correct`, `checker_correct`, `checker_b_correct`, `checker_eq_correct`; `Checker_Ext.checker_ext_correct` | Same set of 51 integer entries plus `ProofIrrelevance.proof_irrelevance` |
| `EUF.valid_check_trans`, `valid_check_congr`, `valid_check_congr_pred`; `LIA.valid_check_micromega`, `valid_check_diseq` | Same 52-entry set |
| `Assumptions.valid_check_hole` | 23 integer entries plus proof irrelevance |
| `DatabaseTrakt.eqbool_Booleqb_embedding`, `eqZ_Zeqb_embedding`, `Natadd_Zadd_embedding_equality` | `Closed under the global context` |
| Existing veriT tests `check_univ`, `fun_const2`, `fun_const2goals`, recompiled from `unit-tests/verit_tactics.v:1-36` | Each has the same 52-entry set as `Euf_Checker.checker_correct`; no leftover certificate-cut axiom |

The full 51-entry integer baseline is:

* `PrimInt63`: `int`, `add`, `addc`, `addcarryc`, `addmuldiv`, `compare`, `div`,
  `diveucl`, `diveucl_21`, `eqb`, `head0`, `land`, `leb`, `lor`, `lsl`, `lsr`,
  `ltb`, `lxor`, `mod`, `mul`, `mulc`, `sub`, `subc`, `subcarryc`, `tail0`.
* `Uint63Axioms`: `add_spec`, `addc_def_spec`, `addcarryc_def_spec`,
  `addmuldiv_def_spec`, `compare_def_spec`, `div_spec`, `diveucl_def_spec`,
  `diveucl_21_spec`, `eqb_correct`, `eqb_refl`, `head0_spec`, `land_spec`,
  `leb_spec`, `lor_spec`, `lsl_spec`, `lsr_spec`, `ltb_spec`, `lxor_spec`,
  `mod_spec`, `mul_spec`, `mulc_spec`, `of_to_Z`, `sub_spec`, `subc_def_spec`,
  `subcarryc_def_spec`, `tail0_spec`.

The concrete EUF/LIA theorem closure is therefore not axiom-free. Proof
irrelevance is already imported/used by the concrete array/bitvector structures
(`theories/structures/FArray.v:14,1476`, `BVList.v:14,304`). Reusing those
semantics carries this baseline; adding an assumed CPC rule theorem would be a
different, forbidden extension. No solver-specific/project axiom appeared in
the audited closure. This is evidence for the named declarations, not an audit
of every possible tactic goal or every dependency in the repository.

Do not infer active proof holes from a raw text search: `PArray.array_ext` is
commented out (`PArray.v:220`); the apparent `Admitted` conversion in
`DatabaseTrakt.v:535` is also inside a comment. `BVList.v`'s `Axiom`/`Parameter`
declarations belong to module type specifications; the instantiated concrete
implementations supply proofs. The reported dependency sets come from Rocq's
actual compiled declarations, not keyword counts.

## 9. Reproduction and remaining work

Commands were run from
`/home/charles/.t3/worktrees/SMTRocq/t3-8cba40a9`. The following validation
commands completed with exit code **0**:

```sh
/home/charles/code/friends/.toolchains/smtrocq-env rocq --version
/home/charles/code/friends/.toolchains/smtrocq-env dune --version
/home/charles/code/friends/.toolchains/smtrocq-env dune build theories
```

The build emitted existing deprecation warnings. The audit input was written
to `/tmp/SmtcoqArchitectureAudit.v` with the following contents (no proofs or
new assumptions):

```coq
From SMTCoq.checker Require Import MainChecker.
From SMTCoq.tactics.preproc Require Import DatabaseTrakt.
Set Printing Width 100.
Print Assumptions _checker__correct.
Print Assumptions Sat_Checker.checker_correct.
Print Assumptions Cnf_Checker.checker_b_correct.
Print Assumptions Euf_Checker.step_checker_correct.
Print Assumptions Euf_Checker.checker_correct.
Print Assumptions Euf_Checker.checker_b_correct.
Print Assumptions Euf_Checker.checker_eq_correct.
Print Assumptions Checker_Ext.checker_ext_correct.
Print Assumptions EUF.valid_check_trans.
Print Assumptions EUF.valid_check_congr.
Print Assumptions EUF.valid_check_congr_pred.
Print Assumptions LIA.valid_check_micromega.
Print Assumptions LIA.valid_check_diseq.
Print Assumptions Assumptions.valid_check_hole.
Print Assumptions eqbool_Booleqb_embedding.
Print Assumptions eqZ_Zeqb_embedding.
Print Assumptions Natadd_Zadd_embedding_equality.
Check @Euf_Checker.checker_b_correct.
Check @Euf_Checker.checker_eq_correct.
Check @Euf_Checker.step_checker_correct.
```

Exact compile command, exit **0**, output
`/tmp/SmtcoqArchitectureAudit.log`:

```sh
/home/charles/code/friends/.toolchains/smtrocq-env rocq compile \
  -Q _build/default/theories/utils SMTCoq.utils \
  -Q _build/default/theories/structures SMTCoq.structures \
  -Q _build/default/theories/checker/fol SMTCoq.checker.fol \
  -Q _build/default/theories/checker/small-checkers/array SMTCoq.checker.small_checker.array \
  -Q _build/default/theories/checker/small-checkers/bva SMTCoq.checker.small_checker.bva \
  -Q _build/default/theories/checker/small-checkers/cnf SMTCoq.checker.small_checker.cnf \
  -Q _build/default/theories/checker/small-checkers/euf SMTCoq.checker.small_checker.euf \
  -Q _build/default/theories/checker/small-checkers/lia SMTCoq.checker.small_checker.lia \
  -Q _build/default/theories/checker/small-checkers/spl SMTCoq.checker.small_checker.spl \
  -Q _build/default/theories/checker SMTCoq.checker \
  -Q _build/default/theories/tactics/preproc SMTCoq.tactics.preproc \
  /tmp/SmtcoqArchitectureAudit.v > /tmp/SmtcoqArchitectureAudit.log 2>&1
```

Existing tactic proof audit, exit **0**, output
`/tmp/SmtcoqArchitectureTacticAudit.log`:

```sh
sed -n '1,36p' unit-tests/verit_tactics.v > /tmp/SmtcoqArchitectureTacticAudit.v
cat >> /tmp/SmtcoqArchitectureTacticAudit.v <<'EOF'
Print Assumptions check_univ.
Print Assumptions fun_const2.
Print Assumptions fun_const2goals.
EOF
/home/charles/code/friends/.toolchains/smtrocq-env dune exec -- rocq compile \
  -Q _build/default/theories SMTCoq \
  -Q _build/default/theories/checker/small-checkers SMTCoq.checker.small_checker \
  /tmp/SmtcoqArchitectureTacticAudit.v > /tmp/SmtcoqArchitectureTacticAudit.log 2>&1
```

The temporary audit sources/logs and compiled `.vo` artifacts are local evidence,
not committed dependencies. This research did not rerun `dune runtest` or claim
the coordinator's previously running full test suite succeeded. No external
Logos/Ethos code was used for this SMTCoq survey; the only external proof data
read was the supplied actual CPC fixture.

Remaining implementation includes the signature compiler/evaluator, checked
term/root translation, strict step traversal/reference checks, EUF/Boolean/LIA
bridges and witness encoders, scoped-assumption handling or explicit rejection,
whole-trace and goal-wrapper proofs, dedicated commands/tactic wiring, negative
tests, full regressions, and measured coverage/performance. None is established
by this report or by the existing baseline build.
