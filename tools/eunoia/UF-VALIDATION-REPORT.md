# Child handoff: UF signature computation and assumption API

Branch: `t3/eunoia-uf4-signature-runtime`.
Worktree: `/home/charles/.t3/worktrees/SMTRocq/t3-a5135a67`.
This report records signature computation coverage, not whole-port completion
or semantic acceptance of an SMT-LIB refutation.

## Verified result

The complete pinned 35-file cvc5 1.4.2 source closure generates 27 selected
rules and 34 helper programs. All 98 steps of the seven actual repository UF
proofs replay with exact ordered premise lookup, including all 15 default
`uf4.cpc` steps and unused steps. Each explicit conclusion, including the final
`false`, is checked. Compiler/runtime code contains no rule-name implementation
switch. The manifest enumerates all 582 excluded rules and source/helper/native
dependencies. Its source hashes were also compared with the private matching
cvc5 installation: 35/35 files matched byte-for-byte.

The additional source `:assumption` field generates an optional pattern.
`derive_assuming fuel typeof name pushed_formula args exact_local_premises`
checks it; ordinary `derive` rejects assumption-bearing rules. Source `scope`
and ordinary `process_scope` are selected. The public ordinary API and
`Symbol`/`Apply` constructors stay stable. Details, including the generic
arithmetic primitive hook and exact flat surface agreement with the merged
adapter, are in `INTERFACE.md`.

## Exact commands and results

All commands below ran from the worktree unless an absolute script path is
shown. No dependency was installed and no shared dune/core/adapter/tactic file
was edited. All dune invocations used `-j2`.

1. `python3 tools/eunoia/regenerate.py` — exit 0; 27 rules, 34 helpers,
   35 sources, 582 excluded rules. Outputs are
   `theories/checker/eunoia/CpcGenerated.v` and
   `tools/eunoia/cpc-manifest.json`.
2. `EUNOIA_KEEP_TEST_DIR=1 tools/eunoia/check-generated.sh > /tmp/smtrocq-generator-uf/check-generated-assumptions-final.log 2>&1`
   — exit 0; 31 Python tests, exact code/manifest regeneration comparison,
   86 kernel-checked Rocq examples (72 runtime including assumption API,
   seven actual fixture replays, seven corrupted/source-mutated trace tests),
   independent recursive `rocq check` of all three regression modules.
   Artifacts: `/tmp/smtrocq-eunoia.SZ9P6coq`.
   The script's exact Rocq compile form is
   `/home/charles/code/friends/.toolchains/smtrocq-env rocq compile -q -Q . SMTCoq.checker.eunoia MODULE.v`
   for each module listed in `VALIDATION.md`. Its final command is
   `/home/charles/code/friends/.toolchains/smtrocq-env rocq check -silent -Q . SMTCoq.checker.eunoia SMTCoq.checker.eunoia.RuntimeTests SMTCoq.checker.eunoia.FixtureTests SMTCoq.checker.eunoia.TraceNegativeTests`.
   `Print Assumptions` reports all 15 audited computational facts closed under
   the global context. No semantic soundness lemma is added by this child.
3. `/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2 theories > /tmp/smtrocq-generator-uf/dune-build-final.log 2>&1`
   — exit 0 on the final sources. Existing notation warnings and the nested
   expression/list scheme warning remain.
4. `python3 /tmp/smtrocq-generator-uf/adapter-compat/check.py > /tmp/smtrocq-generator-uf/adapter-compat/compile-final.log 2>&1`
   — exit 0; each of six module compilations exited 0. This isolated driver
   copies this child's three generator modules and the authoritative parent
   `EunoiaChecker.v`, `EunoiaBridge.v`, `EunoiaAdapter.v`, then uses the adapter
   job's explicit existing SMTCoq dependency mappings. Its exact compiler
   invocations and exits are retained in the log. The adapter's existing
   49 examples compile unchanged. No parent source was modified.
5. `git diff --check` — exit 0. A Python regex audit over the three assigned
   generator Rocq files and every `tools/eunoia/tests/*.v` file found no
   `Admitted`, `admit`, new `Axiom`/`Parameter`, or `Abort` declaration.

An initial local commit attempt returned 128 because Git's index is outside
this worktree's writable root. The user-authorized local commits were then
performed with filesystem escalation, successfully; nothing was pushed.
The exploratory compilation failures are retained in temporary logs where
applicable; the final commands above all succeeded. No global regression
`dune runtest` is claimed by this child; the standalone script is the test
entry point for the generator files and fixtures.

## Remaining work / integration requirements

* Each exact generated step still needs the faithful shared-table adapter and
  `EunoiaLocal` verified multi-operation certificate gate. Replaying syntax is
  not a semantic certificate, and roots in these computation tests are fixture
  data rather than a proof of binding to a user goal.
* The coordinator's scope callback must bind the actual pushed literal and
  exact local clause to CPC surface formulas before `derive_assuming`, bind the
  generated result, and use `EunoiaScope`'s proved conditional invariant and
  discharge. This child implements no semantic scope state machine.
* `tests/TraceReplay.v` / `replay_fixtures.py` deliberately reject scoped proof
  commands. A production scoped reader, omitted-conclusion reconstruction,
  table preparation, local witnesses, and tactic wiring remain outside this
  child. They may not skip any excluded/unused step.
* Arithmetic/rational literal operations, typed/dependent nil elaboration,
  comparison, most string/BV/datatype primitives, nonbinary associative/
  chainable surface elaboration, and general dynamic function-type rule
  matching remain unsupported. The generic `primitive_hook` / `derive_with`
  API is ready for a separate arithmetic job; source relation tables and
  helpers must stay source-generated. Mixed Real/Int formulas need their own
  verified translation to existing semantics.
* Nil spines are internal only. Results are flat surface syntax; singleton
  operator applications remain singleton unless a source helper explicitly
  removes them. The existing adapter rejects these degenerate formula nodes.
  Signed decimal symbols remain distinct from explicit unary negation.
* For build integration the coordinator can add a `runtest` alias invoking
  `tools/eunoia/check-generated.sh`. This child added no shared dune stanza;
  `dune build theories` alone does not run those standalone regression files.

The commit list and final HEAD are supplied in the child response so this
report need not contain a self-referential commit hash.
