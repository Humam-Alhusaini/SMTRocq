# Integer-cast signature computation coverage

This is generated-source computation evidence for ordinary QF_LIA parity and
coefficient bounds, based on parent `4f87e02`. It does **not** establish live
tactic support, whole-proof semantic acceptance, or an object-level Real
interpretation. Every original CPC step still needs the checked binding and
semantic gates. No semantic translation is implemented by this change.

The independent implementation commit is
`5c4e5d616ea64fc10394b6372b00e044c498acd8`
(`feat(eunoia): Compute integer cast conflict and coefficient tightening`).
It contains the selection/generated data and the necessary generic runtime
correction, independently of later semantic integration. The fixture/query/mutation tests are in
`6e97f3282d7210766ac5b8b0cddffb2fb7ae2e16`
(`test(eunoia): Replay integer cast captures and source mutations`). This
report is a separate documentation commit.

## Source declarations and computation correction

The selection increases from **49 to 51 rules**. The complete include closure
remains **35 files / 609 rules**, with **53 helper programs** and **558 excluded
rules**. Both new rules are compiled directly from `rules/Rewrites.eo`:

```lisp
(declare-rule arith-int-eq-conflict ((t1 Int) (c1 Real))
  :premises ((= (= (to_real (to_int c1)) c1) false))
  :args (t1 c1)
  :conclusion (= (= (to_real t1) c1) false))

(declare-rule arith-int-geq-tighten ((t1 Int) (c1 Real) (cc1 Int))
  :premises ((= (= (to_real (to_int c1)) c1) false)
             (= cc1 (+ (to_int c1) 1)))
  :args (t1 c1 cc1)
  :conclusion (= (>= (to_real t1) c1) (>= t1 cc1)))
```

There are no rule-name computation cases, hard-coded source conclusions or
pinned-source edits. Renaming either declaration still compiles generically.
All ordered helper cases remain present, including the actual `$run_evaluate`
`to_real`/`to_int` branches and unexecuted unsupported branches.

**No arithmetic primitive correction is needed.** Existing `eo::to_z` uses
`Qfloor`, so `to_int -3/2` computes to `-2`; existing `eo::to_q` uses `Qred`.
Integer, rational and decimal literal categories remain distinct. In
particular `2/1` is rational syntax, not an integer literal; `2.0` is decimal
syntax and does not satisfy `eo::is_q`. The six unavailable string/BV
primitives remain unavailable; no helper or primitive was added for them.

The first replay after selecting the rules failed at parity `@p7` and bound
`@p13`, both `arith_poly_norm_rel`, after the new rules themselves computed.
The source binds one relation symbol `r`, used at both Int and Real instances.
The prior contextual-hint collector required the two instances to have one
monomorphic arrow type. A faithful query cannot identify Int with Real to
satisfy that constraint.

The compiler now emits `cpc_polymorphic_operators` from **used**
`declare-parameterized-const` declarations having an implicit `Type` binder.
The runtime's new `*_with_polymorphic` hint collectors recognize those syntax
constants and retain the first concrete arrow hint while allowing distinct
application instances. Structural matching still requires the same symbol;
source binder checks, all premise Boolean checks, source requirements, and
result Boolean checking remain in place. Ordinary value/function variables
still require consistent hints; unrelated metadata does not authorize a
polymorphic instance. An explicit query answer still must agree with the
retained binder hint. This is a conservative partial syntax computation, not a
new polymorphic type-system soundness theorem.

Existing runtime function signatures are preserved as wrappers with an empty
polymorphic list. Generated `derive`, `derive_with`, `derive_assuming` and
`derive_assuming_with` signatures are unchanged. The new generated code needs
the updated `EoRuntime.v`; the parent was notified before this shared runtime
change. No `EoSyntax` record or semantic interface changed.

## Actual solver captures

All bytes and inputs are under
`tools/eunoia/tests/integer-fixtures/`; `provenance.json` records exact argv,
version, binary/input/proof hashes, exit status, byte size and wall time.
The solver identifies itself as `cvc5 1.4.2 [git 282d5e0 on branch HEAD]`, with
binary SHA256
`6aecddf466552b83bb5883756c7955e0c9d5ddcc6d7f45b48c2f6e06a741b102`.

Every capture used this exact flag sequence and its tracked input path:

```sh
/home/charles/code/friends/.toolchains/cvc5-1.4.2/cvc5-Linux-x86_64-static/bin/cvc5 \
  --lang=smt2 --dump-proofs --proof-format=cpc \
  --proof-granularity=dsl-rewrite --no-proof-allow-trust \
  --proof-check=eager --check-proofs-complete --tlimit=5000 \
  tools/eunoia/tests/integer-fixtures/lia_parity.smt2
```

Substitute `lia_coefficient_bound.smt2` or `lia_coefficient_scoped.smt2` for the
last argument to reproduce the other captures. All exit **0** with empty
stderr; a second capture of all three matched the retained proof bytes exactly
(`/tmp/smtrocq-integer-recapture.log`).

| Capture | Bytes | Root assumptions | Derived steps including pops | Scope pushes | Maximum nesting |
| --- | ---: | ---: | ---: | ---: | ---: |
| `lia_parity` | 796 | 1 | 8 | 0 | 0 |
| `lia_coefficient_bound` | 1158 | 2 | 16 | 0 | 0 |
| `lia_coefficient_scoped` | 8978 | 1 | 140 | 6 | 3 |

The parent's **9-step / 796-byte parity capture** includes one assumption and
eight derived steps, ending at `@p9`. The fresh tracked capture is byte-for-byte
equal to `/tmp/smtrocq-integer-coverage-solver-options/default.cpc`.
`parity-solver-options.json` retains the parent's four option combinations,
all of which produced identical output. Its rules are exactly `evaluate`,
`arith-int-eq-conflict`, `arith_poly_norm`, `arith_poly_norm_rel`, `trans`, and
`eq_resolve`.

The requested coefficient input is exactly:

```smt2
(set-logic QF_LIA)
(declare-const x Int)
(assert (<= (* 2 x) 3))
(assert (>= x 2))
(check-sat)
```

Its actual `@p8` evaluates `(+ (to_int -3/2) 1)` to `-1`. `@p9` reverses that
equality; `@p10` evaluates the fractional-integrality test to false; `@p11`
uses the two premises in that order to tighten `(>= (to_real (* -1 x)) -3/2)`
to `(>= (* -1 x) -1)`. The final `@p18` is false.

The scoped capture replaces `(<= x 3)` in the repository `lia1.smt2` with
`(<= (* 2 x) 7)`. Its fractional threshold is `-7/2`, tightening to `-3` at
`@p32`. All six pushes/pops, their inner steps, reused local IDs, and the final
`@p137` are retained. No dependency-cone pruning occurs.

Proof SHA256 values:

- Parity: `02abf5f12af803f494dfbfd1e45e021e5bea389a15307f005435cba6fd72e06a`
- Bound: `0aaa695e455aeb43b124496ca55e40d39d694649a17bc09133afe022c0ac4eaf`
- Scoped: `fefb5f1c7f1b535f46719026b9c27d31139ceea1462a36ae1ca03801972c5813`

The **994 old derived steps in 29 fixtures are unchanged**. The total is now
**1158 derived steps in 32 fixtures**, plus **43 scope-push commands**. Counts
exclude root assumptions and include every scope-pop derivation.

## Test metadata and rejection controls

`tests/LiaTraceReplay.v` supplies a deterministic partial structural query for
test declarations. It uses exact literal parsing and declared function types,
homogeneous Int/Real arithmetic, same-sort equality, arithmetic comparisons,
Boolean connectives and typed casts. Cast arities and input sorts are checked.
`to_real` takes Int and returns Real; `to_int` takes Real and returns Int.
Neither rule names nor expected arithmetic results affect the query. Test
support for a declared Real variable is metadata testing only, not permission
for production Real declarations or reification.

Representative required answers for the raw signature computations are:

| Raw term | Syntax sort |
| --- | --- |
| `(* 2 x)` with declared `x : Int` | Int |
| `(to_real (* -1 x))` | Real |
| `(* 3/2 (to_real x))` | Real |
| `(to_int -3/2)` | Int |
| `(to_real (to_int 1/2))` | Real |
| `(= (to_real (to_int 1/2)) 1/2)` | Bool |
| `(= (= (to_real x) 1/2) false)` | Bool |
| `(to_real 1/2)`, `(to_int 2)`, `(+ x 1/2)` | reject |

The trace harness remains computation-only, trusts its supplied root syntax,
and restores saved bindings at scope exit. Its new parameterized replay path
exists solely to run corrupted-source computations through full captures.
Production semantic acceptance does not use this harness or its query.

`IntegerCastTests.v` contains **50 closed computation examples** covering exact
positive/negative/integral floors, cast/literal categories, the two rules,
missing/reordered/wrong/extra premises, changed fractional bounds, wrong
argument sorts, absent queries, unavailable rules, conflicting ordinary hints,
and absent polymorphic metadata. Mutating the actual captured step's declared
result rejects immediately. Appending an unused unknown step rejects the
whole replay.

`integer_mutations.py` corrupts seven actual source declarations/helper bodies
**in memory**, asserts each replacement occurs once, and compiles the full
selection into isolated modules:

1. Conflict's required premise: false -> true.
2. Conflict's result: false -> true.
3. Tightening's second premise: increment 1 -> 2.
4. Tightening's result: `>=` -> `>`.
5. Actual `$run_evaluate` floor case: negate the floor.
6. Actual `$run_evaluate` cast case: `eo::to_q` -> `eo::to_z`.
7. Polynomial relation's nonzero-coefficient source guard: invert its test.

Each corrupted module rejects an entire original parity or coefficient capture;
direct examples also exhibit changed results or rejected original premises.
The old source mutations and negative controls remain enabled. Source case
counts, source hashes and selection-order-independent byte regeneration remain
tested. No production primitive hook or query was introduced for these tests.

## Validation, hashes and logs

Commands from the repository root:

```sh
python3 tools/eunoia/regenerate.py
EUNOIA_KEEP_TEST_DIR=1 tools/eunoia/check-generated.sh \
  > /tmp/smtrocq-integer-check-generated-final.log 2>&1
/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2 \
  theories/checker/eunoia/CpcGenerated.vo \
  > /tmp/smtrocq-integer-generated-dune-build.log 2>&1
git diff --check
```

All four commands exited **0**. The final script also reports **61/61** named
declarations closed under the global context.

Regeneration reports `compiled 51 rules, 53 helpers, 35 source includes; 558
rules excluded`. The validation script runs **47 Python tests**, compares code
and manifest byte-for-byte, compiles every old/new fixture and mutation module,
and independently runs `rocq check` on all ten replay/negative-test modules.
The final retained artifact directory is `/tmp/smtrocq-eunoia.Qdkuh7ys/`.
Existing nested-list induction-scheme warnings in `EoSyntax.v` are unchanged.

The assumption audit is also reproducible directly:

```sh
python3 tools/eunoia/tests/audit_integer_assumptions.py \
  /tmp/smtrocq-eunoia.Qdkuh7ys
```

It checks all **53 new examples** (50 controls plus three complete captures)
and **eight runtime/generated/query entry points**. Observed output is
`61/61 named declarations closed under the global context`; the named results
and complete `Print Assumptions` output are `integer-assumptions.json` and
`integer-assumptions.log` in that directory. No soundness lemma or new proof
assumption is needed; the existing baseline of 52 is untouched.

Earlier diagnostic artifacts were `/tmp/smtrocq-eunoia.qdT6da9J/`: before the
polymorphic correction the new fixtures returned `None` at parity `@p7` and
bound `@p13`. Reusing old compiled mutation modules after replacing the runtime
caused an inconsistent-library-assumptions diagnostic; a fresh complete build
resolved it. A Python source test initially looked for executable `to_int`
instead of the premise pattern `PSymbol "to_int"`; correcting that test gave
47/47 passes. The first successful complete run is
`/tmp/smtrocq-integer-check-generated.log`, artifacts
`/tmp/smtrocq-eunoia.Z7S2pZVb/`; its separate 61/61 audit log is
`/tmp/smtrocq-integer-assumption-audit.log`.

Stable SHA256 values:

- Generated module: `f8093db95b629a04f1d7decfcce48e38b43a04a7155644e0afeee226c3c96b36`
- Manifest: `02e63bf34068fa4db6f3d974d393c17d49aafbcfb081138b69af5940fda8ef09`
- Unchanged `Cpc.eo`: `d13767eb873649c9f40482c99242c42081cf25308962f11c1981ce8e878770ad`
- Unchanged `rules/Rewrites.eo`: `3de9e84915cb0387412e669d9403474f0f14c9f4746a0fd858d288009c55f79e`

All 35 source hashes remain in the manifest. The changes do not touch shared
Dune, theory semantic gates, Adapter, Backend, Search, witness files, or pinned
`.eo` sources. No install, sudo, rc edit, push, PR, or external comment occurs.

## Exact remaining integration obligations

The parent's `/tmp/smtrocq-integer-cast-integration-plan.md` is a **design**, not
implemented acceptance. Its restricted positive-denominator integer embedding
can consume these source computations without changing their raw terms.

1. **Metadata query:** extend the fixed checked Adapter `syntax_typeof` while
   keeping `object_typeof` authoritative. The current fallback handles rational
   and decimal literals and lists, but not raw casts or compound rational
   arithmetic. Add the structural answers above with exact cast/input/arity
   checks and declaration resolution. Do not substitute the test query or add
   a caller-provided type map to tactics. Reject unknown identifiers and
   unsupported Real declarations.
2. **Reader/elaborator:** retain original rational spellings, casts, arguments,
   all premise order and all commands. Keep the existing metadata-literal
   validation using exact `EoArithmetic` parsing, namespace shadowing rejection,
   ordered exported roots, exact claimed-result checks, and every local scope.
   Native reification currently cannot turn these raw Real intermediates into
   accepted object terms; metadata recognition alone cannot fix that boundary.
3. **Pure syntax normalizer:** implement the planned restricted `(n,d)` embedding
   with integer numerator syntax and a positive closed denominator. Preserve
   original Int/Bool terms and the existing right-fold arithmetic structure.
   Translate equality/order by cross-multiplication, preserving sign and
   denominator positivity; `to_real x = 1/2` must map to `2*x = 1`, never
   `x = 0`. Ground `to_int` must use exact floor, including negative fractions.
   Reject non-ground `to_int`, free Real variables/functions, zero/undefined
   division and unsupported syntax. No such normalizer is added here.
4. **Checked binding and semantics:** native reification and checked `binds`
   must use the same normalization of each raw source premise/result against
   authoritative existing integer Atom/Form tables, with a precise binding
   contract. The generated computation still consumes the **original** syntax.
   Every translated local inference still needs the exact existing
   State/Atom/Form/Micromega semantic gate and required certificates, including
   integer parity cuts. Generated syntax equality does not prove a premise's
   truth; a matching false integrality premise must itself be justified.
5. **Scopes and final public proofs:** translate the actual pushed formula and
   exact endpoint, retain every unused step, preserve root proofs and explicit
   negation, and rerun both UF/LIA suites and false/mutation controls. Public
   parity and positive/negative coefficient theorems still need independent
   kernel and assumption audits. This work did not run or claim those public
   proofs or live acceptance. General Real semantics remain outside scope.
