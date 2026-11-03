# Independent trust-boundary review

Reviewed source: `7c2e21df20d4e95ba700149e48d9052233d25d3a` on parent
`smtrocq/cvc5-eunoia`. Review branch: `t3/review-eunoia-trust-boundary`
(initially named `t3/65434544`), branched at that exact commit. Date: 2026-11-03.
Only this report is changed in the review checkout;
reproduction artifacts are outside Git. No implementation, shared build/tactic,
or repository test file was edited. No delegation, installation, push, PR, or
GitHub comment was performed.

**Result: one P2 finding in the older bridge interfaces. No additional findings
within the reviewed production tactic trust boundary.** The finding violates
the requested strict failure-validation policy but does not demonstrate an
unsound theorem. This review is not backend acceptance or a completion claim.

## Finding R1 — P2: the older bridge accepts checker failure fallbacks

Locations:

* `theories/checker/eunoia/EunoiaBridge.v:126–132`: `gate` compares the old
  small checker's output with the requested clause, without distinguishing
  `C._true` as a failure result from an explicit `CTrue` operation.
* `EunoiaBridge.v:65–67`: `decode` admits any nonempty resolution array. It
  does not validate each intermediate link of a longer resolution chain.
* Public exposure: `EunoiaAdapter.v:538–541` (`checked_checker`) and
  `EunoiaScope.v:230–234` (`table_checker`) still instantiate this gate.

Concrete reproductions are in
`/tmp/smtrocq-trust-boundary-review-7c2e21/probe/BoundaryProbe.v`:

1. With valid tables whose formula 2 is `Fiff 0 0`, the clause `[4]` is the
   equality of true with true. `Weaken 1 0 [0]` cannot weaken `[4]` to `[0]`:
   the source literal is absent from the target clause. The old
   `State.S.check_weaken` (`theories/checker/fol/State.v:688–689`) returns
   `C._true`. Nevertheless,
   `@EunoiaBridge.gate ti tf ta fm [[4]] [0] (Witness 2 weak) = true`.
2. This is reachable through the actual generated adapter, not just an
   isolated call to a semantic gate. The example
   `public_checked_checker_accepts_failed_witness` checks generated
   `true_elim` followed by `contra`, with authoritative roots
   `[[4]; [1]]`, and returns `true` while using that failed weakening as the
   first step's witness. It does not replace generated rule evaluation.
3. `bridge_accepts_chain_with_failed_link` supplies exact roots
   `[[0]; [0]; [1]; [1]]` and a four-input `Res`. The first resolution has no
   complementary pivot: `C.resolve [0] [0] = [0;0]`, containing the failure
   fallback. Later links consume those literals and produce `[]`; the bridge
   accepts the final empty clause. Comparing only the final result does not
   expose that failed intermediate operation.
4. The control `local_rejects_same_failed_weakening` evaluates the corresponding
   `EunoiaLocal.execute` call to `None`.

All five computational examples close with `vm_compute; reflexivity; Qed`,
compile successfully, pass independent recursive kernel checking, and have
`Print Assumptions` outputs within the existing baseline. Exact commands and
results appear below. No proof holes or new assumption declarations were used.

Impact: callers of these older exported wrappers can accept malformed semantic
witness operations, including a failed intermediate resolution link. This
violates the requested rule that failures propagate and that only explicit
`CTrue` may authorize the fallback clause. It is **not** evidence of a false
goal being proved: the reproduced roots are inconsistent, the generated CPC
steps are valid, and the old checker proves semantic preservation even when
it returns a tautology. The production tactic uses `EunoiaLocal`, not this
older gate (`eunoiaBackend.ml:145–184, 214`), so this finding does not show a
production tactic bypass.

Recommended fix: either retire these concrete legacy entry points from the
supported interface, or give their gate the same explicit `CTrue` exception,
non-fallback result checks, literal bounds, and binary-resolution restriction
as `EunoiaLocal`. Longer chains should expose and check every intermediate
operation. Add regression controls at the concrete wrappers, including the
generated-adapter reproduction, rather than testing only `EunoiaLocal`.

## Reviewed production chain and conclusions

The source review covered the files named in the review request, the strict
reader, witness producer/serializer, existing `State`, `Terms`, `MainChecker`,
and the relevant existing CNF/EUF/LIA operations. These are source-inspection
conclusions, supported by targeted checks, not a claim of exhaustive testing.

* **Authoritative goal and hypotheses.** `eunoiaBackend.ml:226–297` reifies
  the actual Boolean goal through the existing `Form.of_coq`/`Atom.of_coq`.
  It constructs the opposite-polarity goal root before solver production.
  Supplied facts contribute their actual proof terms; the supplied-lemma
  path constructs the `Forall (C.valid valuation)` proof under the opposite
  goal hypothesis and applies the checked refutation. Root formulas are not
  taken authoritatively from cvc5. `checker_b` constructs its own goal roots;
  `checker_eq` checks the signed `Fiff` and its children. Missing carrier
  instances/cuts reject at `eunoiaBackend.ml:94–113, 251–252`.
* **Export and strict import.** `export` uses the existing SMTCoq printers
  (`eunoiaBackend.ml:54–66`). `eunoiaSolver.ml:49–53, 81–98` bounds output,
  requires successful process termination and an `unsat (...)` envelope,
  but none of those facts proves the goal. `eunoiaProof.ml:303–338, 390–484`
  checks visible premise identities, duplicate/unknown fields, scope balance,
  and the complete response. Unsupported commands/directives reject.
  `eunoiaElaborate.ml:92–186` checks exported declaration types, ordered roots,
  generated results and any printed conclusions. It visits all commands,
  including unused steps and steps after a conflict, before choosing a final
  live parent conflict. Deduplicated solver assumptions retain every original
  authoritative root claim and slot (`49–59`); no distinct root disappears.
* **Reserved names and metadata.** Production obtains signature names from
  the loaded generated inventory, not from the proof (`eunoiaRocq.ml:69–77`).
  Elaboration reserves signature/exported names, limits definitions to private
  `@t<digits>` aliases, rejects unknown unused symbols, and checks lexical
  binders (`eunoiaElaborate.ml:44–47, 60–90, 135–145`). Reader fields have an
  explicit allowlist. Metadata admission does not authorize a semantic rule.
  The adapter's smaller reserved-name list is not by itself a full CPC
  namespace check; production also applies the generated full inventory.
* **Generated computation.** `tools/eunoia/compile.py:139–190, 442–643`
  reads the actual include closure, compiles all selected helper cases,
  binder patterns, requirements, assumptions and conclusions, and emits data
  for the generic runtime. It is not a hard-coded CPC rule switch. This
  review regenerated identical source and manifest and matched all 35 source
  hashes against the privately installed cvc5 1.4.2 signature. The snapshot
  has 48 rules, 53 helpers and 561 explicitly excluded rules.
* **Runtime failure and configuration.** `EoRuntime.v:459–531, 557–636`
  separates completed, stuck and missing computations. A selected helper
  body's failure does not retry a later case. Missing primitives/type queries
  and fuel exhaustion propagate through failure predicates; observing a stuck
  available operation with an EO predicate is intentional source computation.
  Rule binder types, exact premise arity/order, assumptions, requirements and
  result type still run. `CpcGenerated.v:142–148` fixes the production native
  primitive hook. The generic `_with` APIs remain parameterized for extension
  proofs/tests; no CPC field or tactic argument selects them, and even an
  arbitrary hook cannot remove the local semantic gate. `EoArithmetic` handles
  metalevel literals, not a second interpretation of SMT formulas.
* **Adapter and shared interpretation.** `EunoiaAdapter.v:107–253, 347–463`
  uses bounded, strictly ordered Atom/Form table traversal, existing
  `Atom.check_aux`/`get_type`, and exact serialization. `tables_wf` checks
  `Form.check_form`, `Atom.check_atom`, and `Atom.wt`. Premises and result
  clauses must match their exact syntax, lengths and order. Clause encoding is
  deliberately noninjective (a disjunction can be a clause or a singleton
  formula), but explicit clause equality and the local gate keep those cases
  distinct; a singleton false formula cannot satisfy the empty-clause test.
  `EunoiaLocal.valuation` is exactly the existing
  `Form.interp_state_var (Atom.interp_form_hatom ...) (Atom.interp_form_hatom_bv ...)`.
  The tables used for syntax binding and semantic checking are the same.
  The final tactic proof must also convert to the original goal, so a reifier
  disagreement cannot be accepted merely because export and import agree.
* **Live/fresh indices and all steps.** `EunoiaChecker.v:50–70, 166–189,
  244–289` requires live bounded reads, fresh bounded destinations, canonical
  bounded clauses, exact root claims, exact generated conclusions, and a live
  empty conflict. `run` does not stop at the first conflict. No default array
  value supplies a missing premise. The scoped runner has the same checks.
* **Scope snapshots and discharge.** `EunoiaScope.v:65–105` saves the parent
  machine, checks the whole body, fetches the exact endpoint, and restores the
  parent before exporting one fresh result. Only the semantic gate sees
  `S.sort (Lit.neg assumption :: endpoint_clause)`.
  `EunoiaScopedAdapter.v:48–65` runs generated `derive_assuming` with the exact
  encoded pushed literal and unguarded endpoint term. Local bindings expire
  in both reader/elaborator and backend maps; nested exports cannot leak
  beyond their enclosing scope. The structural invariant/guarded-discharge
  proof is independent of whether the generator is correct.
* **Exact local certificates.** `EunoiaLocal.v:73–88, 144–148, 170–254`
  starts a fresh scratch state with precisely the premise clauses and the
  negated conclusion units. A disjunctive premise stays one clause; it is
  never split into asserted disjuncts. All commands and intermediate results
  are checked, including unused commands after a conflict. Accepted operation
  shapes enumerate their clause reads; unsupported shapes, proof-valued holes,
  stale/forward reads, overwritten/out-of-range outputs and noncanonical
  expectations reject. Resolution is binary. Non-`CTrue` fallback results
  reject. `gate_correct` calls the existing `Euf_Checker.step_checker_correct`.
  Witness search is an untrusted producer over those exact roots; its slicing
  removes unused candidate scratch operations, not source CPC steps
  (`search.ml:130–155`). Micromega candidates are recomputed by the old checker.
* **Final proof.** `EunoiaTactic.v:58–124` and
  `EunoiaScopedAdapter.v:149–227` discharge concrete table/gate obligations
  and prove refutation/Boolean-result/equality correctness.
  `eunoiaRocq.ml:53–61` first checks conversion of the complete checker to
  true, then constructs the equality cast; diagnostics cannot authorize
  rejection. `eunoiaBackend.ml:263, 297` uses `Tactics.exact_check`.
  The installed Rocq implementation of `exact_check` checks the proof type
  and goal conversion before refinement. The live/replay lemmas in
  `src/eunoia_backend/tests/integration/{Proof,Public}.v` close with `Qed`.
  No Eunoia no-check tactic or proof-configurable semantic bypass was found.

## Structural order and compatibility limits

Ethos was read locally at
`/tmp/smtrocq-ethos`, commit `f97393ea55f03653689e104d0e9c9010ee17780c`.
`src/type_checker.cpp:1229–1240` implements `eo::cmp` with first-use hashes;
`src/state.cpp:1648–1660` assigns those hashes monotonically. By comparison,
`EoOrder.v:11–21` uses deterministic structural string/application ordering.
The two implementations need not agree on an individual comparison.

This does not invalidate the production semantic theorem: every resulting CPC
conclusion must still pass the exact per-step gate over existing SMTCoq
interpretations. Neither source computation nor the ordering is a semantic
assumption of `gate_correct`. It does limit a claim of faithful Ethos execution
and may affect normalization guards and proof compatibility. There is no proved
equivalence of the two orders or whole normalization algorithm. The explanation
in `tools/eunoia/LIA-VALIDATION.md:113–139` accurately states this replacement,
the intended consistent-order invariant, and the lack of an identical-output
or semantic normalization theorem. No new finding is raised for this expressly
documented design choice. Preserving the gate remains essential.

## Assumption audit and independent evidence

`tools/audit-eunoia-assumptions.py:26–40, 70–109` compares parsed dependency
identities with the exact baseline set. It resolves theorem names inside a
temporary module and closes imports before printing, avoiding the earlier
short-import-name ambiguity. There is no suffix or import-prefix whitelist.
Malformed output and compiler failure reject. The baseline has 52 entries from
the original checker; it is not an assertion that the development is axiom-free.

The independent positive audit covered the three scoped correctness wrappers
and `EunoiaBridge.gate_correct`. All passed with no new assumptions. A negative
audit of existing `Stdlib.Logic.Classical_Prop.classic` compiled successfully
but the audit exited **1**, identifying exactly `Classical_Prop.classic` as new.
Additional parser controls rejected unrelated qualified names sharing baseline
suffixes and malformed output. The five review probes also passed the baseline
comparison. No soundness lemma was added by this review.

Evidence directory: `/tmp/smtrocq-trust-boundary-review-7c2e21/`.
`commands.json` records exact argv, working directories and exit codes;
`prepare.py`, `run-checks.py`, `audit-checks-final.py`, `reader-checks.py`, and
`extra-checks.py` retain the drivers. The snapshot used read-only parent install
artifacts copied from
`/home/charles/.t3/worktrees/SMTRocq/smtrocq-cvc5-eunoia/_build/install/default/lib/coq/user-contrib/SMTCoq/`.
All 36 corresponding installed source files, including all 21 Eunoia source
modules, matched the reviewed checkout byte-for-byte
(`installed-source-comparison.json`). Compiled-object hashes are retained in
`frozen-vo-sha256.json`. The `.vo` files were not rebuilt from scratch here;
the probe's independent recursive kernel check validates their proof terms.

Successful final commands (run from the review checkout unless noted):

```sh
review_dir=/tmp/smtrocq-trust-boundary-review-7c2e21
review_env=/home/charles/code/friends/.toolchains/smtrocq-env

python3 -B "$review_dir/prepare.py"
# 0; matching source snapshot
python3 -B -m unittest discover -s tools/eunoia/tests -p 'test_*.py' -v
# 0; 39 tests, python-generator-tests.log
python3 -B tools/eunoia/regenerate.py \
  --output "$review_dir/CpcGenerated.v" --manifest "$review_dir/manifest.json"
# 0; 48 rules / 53 helpers / 35 files / 561 excluded, regeneration.log
cmp theories/checker/eunoia/CpcGenerated.v "$review_dir/CpcGenerated.v"
cmp tools/eunoia/cpc-manifest.json "$review_dir/manifest.json"
# both 0
"$review_env" rocq c -Q "$review_dir/installed/SMTCoq" SMTCoq \
  -Q "$review_dir/probe" Review "$review_dir/probe/BoundaryProbe.v"
# 0; boundary-probe-qualified.log, including all five Print Assumptions
"$review_env" rocq check -silent -Q "$review_dir/installed/SMTCoq" SMTCoq \
  -Q "$review_dir/probe" Review Review.BoundaryProbe
# 0; boundary-probe-kernel.log; no dependency-admission flags
python3 -B "$review_dir/tools/audit-eunoia-assumptions.py" \
  --import SMTCoq.checker.eunoia.EunoiaScopedAdapter \
  --import SMTCoq.checker.eunoia.EunoiaBridge \
  --theorem EunoiaScopedAdapter.checker_correct \
  --theorem EunoiaScopedAdapter.checker_b_correct \
  --theorem EunoiaScopedAdapter.checker_eq_correct \
  --theorem EunoiaBridge.gate_correct \
  --output-dir /tmp/smtrocq-trust-boundary-audit-positive-7c2e21
# 0; that directory's summary.json
python3 -B "$review_dir/tools/audit-eunoia-assumptions.py" \
  --import Stdlib.Logic.Classical_Prop --theorem classic \
  --output-dir /tmp/smtrocq-trust-boundary-audit-negative-7c2e21
# 1, expected rejection; compiler_exit_code 0; summary.json
python3 -B "$review_dir/tools/audit-eunoia-assumptions.py" \
  --import Review.BoundaryProbe --loadpath "$review_dir/probe" Review \
  --theorem bridge_accepts_failed_weakening \
  --theorem local_rejects_same_failed_weakening \
  --theorem public_checked_checker_accepts_failed_witness \
  --theorem bridge_accepts_chain_with_failed_link \
  --theorem first_link_is_fallback \
  --output-dir /tmp/smtrocq-trust-boundary-audit-probe-7c2e21
# 0; that directory's summary.json
python3 -B "$review_dir/reader-checks.py"
# 0; private ocamlc compile 0; strict reader tests 0, 111 cases
python3 -B "$review_dir/extra-checks.py"
# 0; exact-name/parser controls, 35 installed signature hashes matched,
# forbidden-token rg exited 1 with no matches; git diff --check exited 0
```

The reader driver compiles unmodified reader/test copies under
`$review_dir/ocaml`, with only a module-packaging shim, using exactly:

```sh
cd /tmp/smtrocq-trust-boundary-review-7c2e21/ocaml
/home/charles/code/friends/.toolchains/smtrocq-env ocamlc -o reader-tests \
  eunoiaProof.mli eunoiaProof.ml eunoia_frontend.ml proof_reader_tests.ml
./reader-tests
```

Both exited 0 (`reader-compile.log`, `reader-tests.log`). These are parsing
tests, not proof-acceptance tests. The assumption script copy is byte-identical
to the pinned source; its temporary repository layout points at the frozen
install to avoid rebuilding or changing the parent.

Initial probe/audit setup attempts failed: an implicit table argument was
omitted (compiler exit 1); the audit's output-inside-repository guard rejected
two temporary paths (exit 2); a broad temporary `-Q` mapping shadowed the
SMTCoq mapping and caused compile/audit/kernel failures (exit 1). Corrected
commands use the isolated `probe` directory and external audit directories as
shown above. Failed setup attempts are not counted as passing validation.
Repeated log stems contain the final successful run; `commands.json` retains
the failed argv/status entries too.

I also inspected, without rerunning or extending their scope:

* `/tmp/smtrocq-generated-scoped-integrated-assumptions/summary.json`: compiler
  exit 0 and no new assumptions for five concrete correctness declarations
  and three exported public proofs. It is not an audit of all future goals.
* `/tmp/smtrocq-generated-scoped-kernel-recheck-status.json`: recorded recursive
  kernel check exit 0, 33.897 seconds, for scoped adapter and backend
  `Proof`/`Public` modules. This is parent-provided evidence, separate from the
  independent probe check above.
* `/tmp/smtrocq-generated-lia-default-runtest.log` and the pinned
  `tools/eunoia/{dune,check-generated.sh}`: the alias runs 39 Python tests,
  exact regeneration, standalone compilation of runtime and source-mutation
  controls, and kernel checks of fixture/computation modules. The 962 steps
  in 28 fixtures establish generated syntax computation, **not whole-proof
  acceptance through the tactic and semantic gates**. I did not rerun the full
  benchmark or full repository regression build.

## Incomplete work and required fresh review

The known theorem-local quantified-carrier universe anomaly, negative-predicate
double-negation serialization failure, and unsupported `Fiff` to atomic
`BO_eq Tbool` bridge for Boolean function arguments are accepted coverage gaps,
not proof-soundness findings. They were not reproduced here. The optional
common-reifier change `fbfbe26` is already in the reviewed source; its production
wiring is still pending at this pin. The reported twenty individual positive UF
probes and two rejected false controls do not establish acceptance of the entire
UF file, quantified-carrier regression, or a meaningful LIA suite.

This review does not cover later implementation-child changes. After
integration, a new review should inspect the actual diff in
`src/eunoia_backend/{eunoiaBackend,eunoiaRocq,eunoiaElaborate}.ml`,
`src/eunoia_witness/{search,certificate}.ml`,
`src/common/smtlib2_genConstr.ml`, and `EunoiaAdapter.v`, plus any changed
local/scoped gate, generator/runtime, or tactic/dune wiring. In particular:
check universe instantiation against theorem-local carriers; exact preservation
of explicit negations and the corresponding witness formula cases; preservation
of goal/hypothesis proof-term binding; and agreement between newly admitted
syntax and the existing Atom/Form interpretation. Re-run the relevant complete
UF/LIA positives, false/corrupted/unused-step controls, audits of the actual
exported proofs, and recursive kernel checks on the final installed revision.
R1 also needs a fresh targeted recheck after the parent fixes or retires the
legacy interfaces. Coordinator integration and overall backend completion
remain outside this review.
