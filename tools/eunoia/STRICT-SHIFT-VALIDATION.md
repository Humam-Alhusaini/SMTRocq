# Strict-shift integer tightening: generator handoff

This is a source-computation extension, not live semantic acceptance of the
benchmark theorem or completion of the Eunoia port. The semantic gate must
still check every result against its exact premises and conclusion using the
existing SMTCoq integer semantics and checkers.

## Minimal source change

Base: `5523d5ed65fa6fa34a1bbd7ca7a64b8f0588d4ca`.
Child branch: `t3/strict-shift-generator-rules`.
The generator-only commit is `f96adaed4736026a113d858b3f5cfe10c80e1a5f`.

`rules.txt` adds only `arith-geq-tighten`. The unmodified actual declaration
at `signatures/cpc/rules/Rewrites.eo:94` is:

```lisp
(declare-rule arith-geq-tighten ((t1 Int) (s1 Int))
  :args (t1 s1)
  :conclusion (= (not (>= t1 s1)) (>= s1 (+ t1 1)))
)
```

`compile.py` and the runtime are unchanged. Both integer binder checks, exact
two-argument/no-premise matching, output type checking and fuel checks remain.
This declaration has no additional `:requires` guards to weaken. Its conclusion
and integer increment are compiled through the same generic expression and
dependent-nil machinery as other selected rules. No rule-name execution switch
or handwritten implementation was added.

`CpcGenerated.v` gains exactly one generated rule entry. The manifest now has
**49 selected rules, 53 helpers, 560 excluded rules and 35 source files**. Its
primitive inventory is unchanged. No other missing rule occurs in the new
trace, so no additional normalization declaration was selected.

All 35 vendored files were compared by SHA256 with the installed matching
cvc5 1.4.2 closure and match. The unchanged entry `Cpc.eo` SHA256 is
`d13767eb873649c9f40482c99242c42081cf25308962f11c1981ce8e878770ad`;
`rules/Rewrites.eo` is
`3de9e84915cb0387412e669d9403474f0f14c9f4746a0fd858d288009c55f79e`.
The solver reports `cvc5 1.4.2 [git 282d5e0 on branch HEAD]`. Neither Logos nor
Ethos was used in this extension.

## Actual solver capture and complete replay

The retained public benchmark failure is at
`/tmp/smtrocq-lia-milestone-benchmark/runs/cvc5_eunoia/lia_strict_shift/1/`.
The new input `tests/fixtures/lia_strict_shift.smt2` negates its Boolean result:

```lisp
(set-logic QF_UFLIA)
(declare-fun op_1 () Int)
(declare-fun op_0 () Int)
(assert (not (= (= (< op_0 op_1) (<= op_0 (- op_1 1))) true)))
(check-sat)
(exit)
```

Here `op_0` denotes `x` and `op_1` denotes `y`. The retained declaration order
reproduces the reported `@p20` instance, including the exact argument tree
`(+ op_1 (* -1 op_0))` and bound `1`. The input SHA256 is
`a8ee41294219f553e3a8e61dacdfc4d2f1110b4c7ac8f93dc48dc61ccc956be6`.

The exact solver command, run from the repository root, was:

```sh
/home/charles/code/friends/.toolchains/cvc5-1.4.2/cvc5-Linux-x86_64-static/bin/cvc5 \
  --lang=smt2 --dump-proofs --proof-format=cpc \
  --proof-granularity=dsl-rewrite --no-proof-allow-trust \
  --proof-check=eager --check-proofs-complete --tlimit=60000 --rlimit=10000000 \
  tools/eunoia/tests/fixtures/lia_strict_shift.smt2
```

Exit code: **0**, `unsat` and CPC output, empty stderr. The proof is retained as
`tests/fixtures/lia_strict_shift.cpc`, SHA256
`9df2cf20d525f4d51496b67b27803f98f6d8397371dfe00422f17cb9e4c97f37`.
`tests/fixtures/provenance.json` records the argv, input/proof hashes and exit.
The solver status is not treated as proof evidence.

There is one root, **32 steps**, no push/pop, and final `@p33 false`.
The trace uses 15 rule names, with only `arith-geq-tighten` newly selected.
`replay_fixtures.py --scoped` retains every command, producing
`LiaFixtureTests.lia_strict_shift_all_steps`. The test uses the existing
`LiaTraceReplay.lia_query` with the actual two integer declarations; no query
or replay harness change was needed. This partial structural query types the
arithmetic expressions as `Int`, relations/negations/equalities as `Bool`,
and `Int`/`Bool` as `Type`. Tests explicitly check both new rule arguments and
its exact result type. Query information is computation input, not semantics.

All **29 original/reduced fixtures now contain 994 computed steps**, including
37 pops and 37 separately tracked pushes. The original group comprises seven
UF proofs (98 steps), seven old LIA proofs (379 steps), and this new LIA proof
(32 steps). The reduced group retains all fourteen proofs (485 steps).
Unknown/unused commands are not removed to obtain these counts.

## Regression coverage

Three new Python tests check actual source mutation, generic compilation under
a fresh rule name, and exact capture counts/`@p20` arguments. The existing
provenance test also verifies the added capture and source-input hashes. The
Python total is **42 passing tests**.

`tests/StrictShiftTests.v` adds **27 computation examples**. Positive checks
include the exact benchmark argument, symbolic and negative integer bounds,
the argument/result queries, and a complete-trace diagnostic. Rejection checks
cover Real/Bool/mixed/unknown arguments, missing/extra arguments, unexpected
premises, unavailable type information, exhausted fuel and an inappropriate
assumption on an ordinary rule.

The isolated mutated signature changes the actual declaration's increment
from `1` to `2`, with all other selected declarations retained. It computes
the altered result, which is compared against the production computation.
The mutation is generated only in the temporary validation directory and is
never part of the production rule table.

Actual-trace mutations reject an incorrect bound (the next `trans` fails at
`@p21`), a rational bound, an extra premise, a declared conclusion with the
wrong increment, an unavailable replacement rule, and an unused unknown step.
The type/premise/conclusion/rule mutations fail at `@p20`. The complete
unchanged trace still computes `false` at `@p33`.

## Validation and first failure

The first standalone run exited **1** in the test-only source-mutation example.
Its mutated signature had been compiled with only the new rule selected, so
it lacked the metadata for the compound `*` argument and correctly returned
`None`. The harness now compiles the mutated declaration with the full selected
signature, matching the production input syntax support. No runtime, binder,
guard or production source was relaxed. The first log is retained at
`/tmp/smtrocq-strict-shift-check-generated-first-failure.log`, and its artifacts
at `/tmp/smtrocq-eunoia.8m8y4uZi/`.

The following commands, from the repository root, exited **0**:

```sh
python3 tools/eunoia/regenerate.py
EUNOIA_KEEP_TEST_DIR=1 tools/eunoia/check-generated.sh \
  > /tmp/smtrocq-strict-shift-check-generated.log 2>&1
/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2 \
  theories/checker/eunoia/CpcGenerated.vo \
  > /tmp/smtrocq-strict-shift-generated-dune-build.log 2>&1
python3 -m unittest discover -s tools/eunoia/tests -p 'test_*.py' -v \
  > /tmp/smtrocq-strict-shift-python-tests.log 2>&1
```

The standalone script regenerates and byte-compares code/manifest, executes
all 42 Python tests, compiles all direct and complete fixture computation
proofs, then runs independent `rocq check` on all eight test modules. Its
retained final directory is `/tmp/smtrocq-eunoia.XLLcqQ2z/`. Existing
`EoSyntax.v` nested-list induction-scheme warnings occur; no compilation or
kernel-check failure remains in that run.

After strengthening the source-mutation inequality example to compare both
actual computations, the final test file was recopied, recompiled, audited,
and kernel-rechecked by `/tmp/smtrocq-strict-shift-final-validation.sh`.
The script and all three commands exited **0**. Its output is
`/tmp/smtrocq-strict-shift-final-validation.log`; the exact
commands in that script, after copying the current test file and changing to
`/tmp/smtrocq-eunoia.XLLcqQ2z/`, are:

```sh
/home/charles/code/friends/.toolchains/smtrocq-env rocq compile -q \
  -Q . SMTCoq.checker.eunoia StrictShiftTests.v
python3 /tmp/smtrocq-strict-shift-audit.py /tmp/smtrocq-eunoia.XLLcqQ2z
/home/charles/code/friends/.toolchains/smtrocq-env rocq check -silent \
  -Q . SMTCoq.checker.eunoia SMTCoq.checker.eunoia.StrictShiftTests
```

The new examples and fixture proof each have `Print Assumptions`. The named
audit's `strict-shift-assumptions.json` and `strict-shift-assumptions.log` are
in that retained directory: **28/28 pass**, each closed under the global
context. `git diff --check`, the changed-path ownership audit, and the audit
of added proof text also passed. No shared file was changed.
No semantic soundness lemma, assumption, axiom or proof placeholder is added.

## Compatible integration and incomplete work

No shared Dune, runtime, adapter, witness, backend or tactic file is changed.
The current `tools/eunoia/dune` already declares `(source_tree tests)`, so the
new fixture/test are picked up by its existing alias with no stanza edit.
The public `derive`, `derive_with` and scoped APIs are unchanged. The compiled
rule uses the existing query and arithmetic/syntax data; no new primitive is
required. Retain the coordinator's sigma preservation, exact negation,
signed-root export, right-fold lowering and transparent shared default fuel.

The LIA owner can cherry-pick the generator commit (and optionally the separate
fixture/test/report commit), rebuild the generated module, and rerun the
original public theorem unchanged:

```coq
forall (x y : Z), Bool.eqb (x <? y) (x <=? y - 1) = true
```

The intended source result at `@p20` is exactly:

```lisp
(= (not (>= (+ op_1 (* -1 op_0)) 1))
   (>= 1 (+ (+ op_1 (* -1 op_0)) 1)))
```

Live semantic acceptance, witness/certificate support for this and subsequent
steps, the original public theorem's final assumption audit, the full LIA
suite and composed regression/benchmark work remain with the LIA owner and
coordinator. This child did not run or claim that live proof. Source replay
alone does not establish it, and the 560 excluded rules remain unsupported.
