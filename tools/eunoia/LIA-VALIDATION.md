# LIA signature computation: integration report

This implements signature computation, not semantic acceptance of CPC proofs.
No end-to-end backend or port completion is claimed. Every computed result
still needs the existing SMTCoq adapter, exact premises, scoped core and local
semantic certificate gate. In particular the relational normalization tests
can supply a syntactically shaped but unproved premise: signature computation
alone does not establish that premise.

This report records the preceding 48-rule LIA tranche. The subsequent minimal
integer-tightening extension brings the current selection to 49 rules without
changing its 53 helpers; see [STRICT-SHIFT-VALIDATION.md](STRICT-SHIFT-VALIDATION.md)
for the added actual trace, checks and remaining integration work.

## Source and scope

* Child branch: `t3/lia-signature-computation`.
* cvc5 1.4.2 binary reports git `282d5e0`, privately installed under
  `/home/charles/code/friends/.toolchains/cvc5-1.4.2/`.
* The vendored 35-file include closure remains unchanged. The entry
  `Cpc.eo` SHA256 is
  `d13767eb873649c9f40482c99242c42081cf25308962f11c1981ce8e878770ad`,
  identical to the supplied installed 1.4.2 signature. Every closure hash is in
  `cpc-manifest.json`.
* Ethos inspected read-only at `/tmp/smtrocq-ethos`, commit
  `f97393ea55f03653689e104d0e9c9010ee17780c`.
* The arithmetic child's commits `af2c933` and `dcc63ec` were cherry-picked as
  `92d267c` and `1ec41f3`; `EoArithmetic.v` was not edited. Before those commits
  became available, validation used temporary copies of that child's module
  from sibling worktree `../t3-47fa7690` in `/tmp/eunoia-lia-dev/`.

The initial selection had 30 rules. The final selection has **48 rules,
53 programs, and 561 explicitly excluded rules**. Additions are
`arith-elim-gt`, `arith-elim-leq`, `arith-elim-lt`, `arith-eq-elim-int`,
`arith-leq-norm`, `arith_mult_neg`, `arith_poly_norm`, `arith_poly_norm_rel`,
`arith_sum_ub`, `int_tight_ub`, `bool-impl-true2`, `cnf_and_neg`, `implies_elim`,
`not_and`, `not_implies_elim1`, `not_implies_elim2`, `not_or_elim`, `reordering`.
The three parent-added Boolean equality/double-negation rules are retained.
All helper cases, including arithmetic relation tables, are generated from
source. The Python tests compare the number of emitted cases with each
source declaration and exercise a changed source relation table.

`cpc_signature_names` exports 347 constant, parameterized-constant and
alias/macro names from the full closure plus native type/Boolean/meta-list
syntax. It excludes rule/program names, binders, and the private capability
hook. This is a namespace reservation inventory, not a supported-term claim.

## Generic runtime changes

* `Symbol` and `Apply`, and the public `derive`/`derive_assuming` argument types,
  are unchanged. The expression/pattern IR adds `ENil` and `PNil`.
* `cpc_nils` contains source nil bodies and both constructor-domain patterns:
  element and list-tail. `resolve_nil` binds implicit type parameters against
  the appropriate queried type. This distinction matters for typed lists:
  the element has type `Int`, but the tail has type `(@TList Int)`.
  Surface elaboration and constructor expressions use the element domain;
  nil patterns, list operands and `eo::nil` use the tail domain, following
  Ethos `TypeChecker::evaluateNil` and `evaluateLiteralOpInternal`.
* `+` and `*` obtain integer or rational zero/one from the generated
  `$arith_mk_zero`/`$arith_mk_one` cases. Polynomial and heterogeneous-list
  spines preserve order, duplicates, and the exact source terminators.
  Typed-list nil matching, empty reversal and zero repetition have tests.
  Unary/binary `-` arities come from the overloaded declarations.
* `derive` and `derive_assuming` now use `default_primitive`, dispatching to
  `EoArithmetic.eval` and `EoOrder.eval`. `derive_with` and
  `derive_assuming_with` remain available, including explicit `no_extension`.
* Custom hooks may answer `eo::supports [Symbol name]`. `evaluate_computation`
  returns `Done value`, `Stuck`, or `Missing reason`. Failure of an available
  conversion of a variable is observable by EO kind predicates. A missing
  primitive, missing type query or exhausted fuel propagates through those
  predicates. For example, without arithmetic the probe
  `eo::is_q (eo::to_q x)` returns `Missing "eo::to_q"`, never false.
* Function-binder type hints are inferred from the exact matched application
  context and queried argument/result types. Hints are indexed by binder ID,
  must agree at repeated occurrences, and must agree with explicit query
  results. This avoids inventing a monomorphic type for bare `=` or `>=`.
  Program annotations retain the existing metadata treatment; rule binder
  checking remains mandatory.

The nil-body evaluator uses the closed-nil evaluator for nil-body helper
execution. All reached arithmetic and typed-list nil bodies work in that
fragment. A future nil body recursively requiring another dependent nil is
not generally elaborated; it fails closed. No missing BV/string primitive is
made available by generating its nil body.

## Exact surface type-query requirements

After canonical aliases and internal spines are reversed, the external query
sees surface syntax. For the seven UF and LIA fixtures it must type:

```text
Symbol "@List"                  -> Some (Symbol "Type")
Symbol "@list.nil"              -> Some (Symbol "@List")
(@list t1 ... tn)                -> Some (Symbol "@List")
0, -1, x, (+ x y), (* -1 x)     -> Some (Symbol "Int")  [x,y : Int]
(- x), (- x y)                   -> Some (Symbol "Int")  [x,y : Int]
(>= (+ x (* -1 y)) 0)            -> Some (Symbol "Bool")
(not (>= (+ x (* -1 y)) 0))      -> Some (Symbol "Bool")
Int, Bool                       -> Some (Symbol "Type")
```

`@list` is a heterogeneous meta-list, not an SMT list with an invented object
semantics. It is used in resolution arguments; those exact elements are still
checked by the generated helpers. No polynomial/monomial/pair/typed-list type
query is needed by these fixtures' live helper computations. Closed-nil
lookup ignores a failed optional element query. A query for a bare polymorphic
relation can return `None`: application-context hints supply its instantiated
function type. The LIA test query deliberately returns `None` for bare
relations and all fixtures still replay.

For future typed-list inputs the syntax query needs, for example,
`(@tlist.nil Int) : (@TList Int)` and
`(@tlist x y) : (@TList Int)` for integer elements. These are metadata types,
not integer atoms. If rational syntax is admitted it must distinguish literal
categories: `0/1 : Real`, `0 : Int`; `Real : Type`. That does not authorize
mapping Real object formulas to the existing integer interpretation.

## Ordering contract and limits

Ethos `src/type_checker.cpp:1229` implements `eo::cmp a b` as
`getHash(a) > getHash(b)` after requiring non-stuck arguments.
`src/state.cpp:1648` shows that `getHash` assigns monotonically increasing,
unique first-use IDs in a map. This is not a numeric comparison, structural
hash, hash with collisions, or mandated lexical symbol order. In a fixed run
it gives a consistent strict total order on distinct terms that have received
IDs; the order depends on history. `$compare_var a b` is `eo::cmp b a`.

The replacement uses a deterministic structural lexicographic term order:
`Symbol` before `Apply`, lexical ASCII string order within symbols, then
function and argument subtrees. The required mathematical invariant for these
polynomial helpers is a consistent strict total order with equality exactly
structural equality, used for every insertion/merge and both compared normal
forms. This preserves canonical variable-factor lists and sorted polynomial
keys. It must not sort object-level operand lists, erase duplicates, compare
numeric values, or switch order between normalizations.

This is an explicit replacement for Ethos's history-dependent order, **not**
a claim of identical internal polynomial list output or of a formal
normalization/semantic-soundness theorem. The selected arithmetic rules use
those lists internally in equality guards; they return the original source
rule expressions. Kernel computation tests cover cancellation, reordered
sums/products, multiplication of variable monomials, invalid coefficients,
and actual fixture instances. Formal semantic acceptance remains the existing
per-step checker/gate's responsibility.

## Retained fixtures and checks

`tests/fixtures/` retains seven original UF fixtures (98 steps) and seven fresh
LIA fixtures (379 steps including 12 pops, plus 12 pushes). Each proof byte
hash, input hash, exact solver argv and exit status is in `provenance.json`.
The LIA capture command, for each `i=1..7`, was exactly:

```sh
/home/charles/code/friends/.toolchains/cvc5-1.4.2/cvc5-Linux-x86_64-static/bin/cvc5 \
  --dump-proofs --proof-format=cpc unit-tests/files/lia$i.smt2
```

All seven exited 0 with `unsat` and empty stderr. This by itself was not
considered evidence of proof validity.

`tests/reduced-fixtures/` retains fourteen additional fresh captures made with
all of the following options before the input filename:

```text
--dump-proofs --proof-format=cpc --proof-granularity=dsl-rewrite
--no-proof-allow-trust --proof-check=eager --check-proofs-complete
--simplification=none --no-static-learning --no-ite-simp
--no-unconstrained-simp --no-repeat-simp
```

All fourteen exited 0 with empty stderr and match the parent's captures in
`/tmp/smtrocq-eunoia-capture/reduced/` byte-for-byte. Their exact argv/hashes are
in that directory's retained `provenance.json`. They contain 485 steps including
25 pops, plus 25 pushes. In particular reduced UF6 has six computed steps and
one push; none is omitted. The new source selection also covers `cnf_and_neg`
in reduced UF5 and `arith-eq-elim-int` in reduced LIA2/LIA7.

The test-only decoder/replayer now handles push/pop snapshots, reused local
IDs, exact local premises and `derive_assuming`. It does not replace the
production reader or scoped semantic core. Every step, including unused ones,
is computed. Pops restore the saved environment before inserting only the
computed discharged formula. Unbalanced scopes and leaked local IDs reject.

There are 37 new direct LIA computation examples, nine negative scoped/actual
trace examples, 28 full-fixture computation proofs, and 39 Python tests.
Examples test nonzero/sign restrictions, wrong polynomial coefficients,
changed endpoints, non-unit multiplicative tails, scaling guards (including
positive coefficients retaining a negative guard), empty/invalid sum inputs,
strictness and exact sum order/multiplicity, unavailable conversions and type
queries. Mutated source relation tables change the output. Mutated actual
traces reject changed coefficients, premises, scaling direction, sum
multiplicity, pop rules, unknown unused steps and inaccessible local IDs.

## Reproduction and integration boundaries

Run from the repository root:

```sh
python3 tools/eunoia/regenerate.py
EUNOIA_KEEP_TEST_DIR=1 tools/eunoia/check-generated.sh
/home/charles/code/friends/.toolchains/smtrocq-env dune build theories -j2
```

The standalone script runs all Python tests; regenerates and byte-compares
both generated Rocq and manifest; generates source-mutated signatures and all
fixture proofs; compiles isolated modules using the private wrapper; and runs
`rocq check -silent -Q . SMTCoq.checker.eunoia` on all seven computation test
modules. Its full module/argv lists are in `check-generated.sh`.
Every new computation example and each fixture proof has `Print Assumptions`.
No semantic soundness lemma was added; no new assumptions or proof holes are
introduced by this task. Successful audit outputs are closed under the global
context. Detailed final results/log paths are recorded with the local commits
in the handoff.

No shared dune, core, adapter, local gate, witness, backend or tactic file was
edited. The parent's shared `tools/eunoia/dune` dependency fix must be retained
when integrating. `EoOrder.v` and the arithmetic child modules must be available
before compiling the generated module (the production theory discovers them).
The standalone script automatically uses those real production modules.

Unavailable primitives explicitly listed in the generated manifest are
`eo::concat`, `eo::extract`, `eo::find`, `eo::len`, `eo::to_bin`, `eo::to_str`.
Their source branches remain present. Reaching an unavailable primitive fails
closed with a diagnostic; full string/BV/datatype/quantifier computation,
general attributed operator elaboration, noncanonical literal spellings at the
reader boundary (the fixtures use cvc5 printer-normalized tokens), and rules
excluded from `rules.txt`
remain unsupported. Mixed Real/Int semantic certificates, production namespace
and type-query integration, scoped backend replay, tactic and semantic gate
integration, and live checked benchmark coverage remain coordinator-owned and
incomplete here. No push, PR or GitHub comment was made.


Final validation results on the finished production code:

| Exact command / check | Exit/result | Artifact |
| --- | --- | --- |
| `python3 tools/eunoia/regenerate.py` | 0; 48 rules, 53 helpers, 35 includes | checked-in Rocq and manifest |
| `EUNOIA_KEEP_TEST_DIR=1 tools/eunoia/check-generated.sh` | 0; 39 Python tests, exact regeneration, 28 fixture proofs, direct/negative examples, independent kernel recheck | `/tmp/eunoia-lia-handoff-validation.log`, `/tmp/smtrocq-eunoia.2e7XjAvf/` |
| `/home/charles/code/friends/.toolchains/smtrocq-env dune build theories -j2` | 0 | `/tmp/eunoia-lia-handoff-dune-build.log` |
| Forbidden-declaration audit of seven owned Rocq files | 0; no prohibited tokens | `/tmp/eunoia-lia-handoff-audit.txt` |
| `git diff --check` | 0 | local diff |

The actual-trace guard mutation test was then strengthened to change the
coefficient of the **selected** `arith_mult_neg` rule from `-1` to `1`, rather
than changing its name to an excluded rule. The final test-only change was
compiled and independently kernel-rechecked using these exact commands in
`/tmp/smtrocq-eunoia.2e7XjAvf/`:

```sh
/home/charles/code/friends/.toolchains/smtrocq-env rocq compile -q \
  -Q . SMTCoq.checker.eunoia LiaTraceNegativeTests.v
/home/charles/code/friends/.toolchains/smtrocq-env rocq check -silent \
  -Q . SMTCoq.checker.eunoia SMTCoq.checker.eunoia.LiaTraceNegativeTests
```

Both succeeded (exit 0); all nine assumption reports were closed.
Log: `/tmp/eunoia-lia-final-negative-validation.log`.
The full script's 82 assumption reports were also closed. No full child-branch
`dune runtest` result is claimed: retain the parent's shared dependency fix
`f6fd451` when integrating these commits. Earlier intermediate runs that were
superseded or failed during development are not acceptance evidence.
