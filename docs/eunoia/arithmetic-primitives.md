# Eunoia arithmetic literal primitives

This is syntax-to-syntax computation for the Eunoia meta-language. It provides
no interpretation of object-level SMT operators, no CPC rule checker and no
end-to-end LIA coverage claim. The generated signature remains responsible for
helper programs and rules; the existing SMTCoq semantic certificate gate must
still check every source rule result against its premises and conclusion.

## Pins and evidence

* Ethos source: `/tmp/smtrocq-ethos`, commit
  `f97393ea55f03653689e104d0e9c9010ee17780c`.
* cvc5: 1.4.2, binary build commit `282d5e0`, matching signature root
  `/home/charles/code/friends/.toolchains/cvc5-1.4.2/cvc5-cvc5-1.4.2/proofs/eo/cpc`.
  `Cpc.eo` SHA256:
  `d13767eb873649c9f40482c99242c42081cf25308962f11c1981ce8e878770ad`.
* Contract sources: Ethos `src/literal.cpp:182` (`Literal::evaluate`),
  `src/type_checker.cpp:164` (arities), `src/type_checker.cpp:1239`
  (literal-kind predicates), `src/state.cpp:776` (variadic folding),
  `src/lexer.cpp:294,402` and `src/expr_parser.cpp:363` (literal parsing),
  `src/util/integer.cpp:132` (Euclidean division),
  `src/util/rational.cpp:56` (rational printing).
* The read-only expanded UF syntax/runtime were inspected at
  `/home/charles/.t3/worktrees/SMTRocq/t3-a5135a67/theories/checker/eunoia/`.
  Only `Symbol string | Apply term term` is required here. No dependency on
  that runtime's expression constructors is introduced.

The implementation follows the pinned C++ code. For example, the native
integer quotient is Euclidean, although the pinned user manual describes it
as floor division without qualifying negative divisors.

## API and integration

`theories/checker/eunoia/EoArithmetic.v` exports module `EoArithmetic`:

```coq
supports : string -> bool
eval : string -> list EoSyntax.term -> option EoSyntax.term
result := Unsupported | Failed | Value : EoSyntax.term -> result
dispatch : string -> list EoSyntax.term -> result
parse : string -> option literal
normalize : EoSyntax.term -> option EoSyntax.term
```

Use `dispatch`, or check `supports` **before** calling `eval`. `None` for a
recognized name denotes failed computation, including unsupported overloads,
wrong arity, malformed numeric input, and division by zero. It must not select
a different evaluator or become a successful symbolic application, identity,
or Boolean false. An unrecognized name is `Unsupported`. The two dispatcher
lemmas prove this distinction. `eval` itself returns `None` for unknown names.

Operands must already have undergone the runtime's expression evaluation.
`is_z` and `is_q` are explicit kind observations: they return false on an
ordinary nonliteral term and on other literal categories. This does not make
an arbitrary failed native call into a successful value. The coordinator must
preserve the pinned language's handling of stuck computations in helpers such
as `$get_arith_poly_norm`, which observes `(eo::is_q (eo::to_q a))` when `a`
is an opaque object term. This module does not implement expression reduction,
`eo::is_ok`, `eo::is_eq`, or let-bound stuck expressions.

Literal spellings must retain their category: `1`, `1/1`, and `1.0` are distinct.
`normalize` canonicalizes numeric spellings while preserving that category;
it returns `None` on nonnumeric terms. Use it only after literal classification
at ingestion, before generic syntactic equality or pattern matching. Symbol
syntax has no quote/literal tag: upstream parsing must reject ambiguous quoted
numeric symbols rather than erase their quoting into a numeric `Symbol`.

Ethos defaults to converting **proof-body** decimals to rationals, but does not
apply that option while loading signature files; optional numeral normalization
is separate. These parser options belong at ingestion, not inside arithmetic
operations. This API preserves the supplied category. Decimal output uses an
exact canonical terminating decimal (`1.0`, `-0.005`, etc.) because Ethos's
`toStringDecimal()` prints a fraction and would lose the DECIMAL kind if
reparsed. Differential tests compare native values including their kinds, not
the native diagnostic printer's text.

The shared dune stanza already discovers new `.v` files. The coordinator should
add `EoArithmeticTests.vo` to the eunoia `runtest` alias, import the module into
the expanded runtime, and route its native names through this dispatcher.
This child did not modify shared dune, syntax, runtime, generator, adapter,
backend, scope, witness or tactic files.

## Implemented contract

All numbers use arbitrary precision `Z`/`Q`; decimals store an exact integer
numerator and a decimal scale. There is no floating point conversion or
machine-integer truncation. Rational results are reduced with positive
denominator; zero is `0/1` and integral rationals retain `/1`. Integer results
have no leading zeroes or negative zero. Decimals retain a point and at least
one fractional digit, removing redundant trailing zeroes.

| Native names | Arity | Literal behavior |
| --- | --- | --- |
| `eo::is_z`, `eo::is_q` | 1 | Test NUMERAL / RATIONAL kind respectively, independent of object type; DECIMAL satisfies neither. |
| `eo::add`, `eo::mul` | at least 2 | Left fold; operands must all have the same arithmetic literal kind. No zero-argument identity or unary shortcut. |
| `eo::neg` | 1 | Negate; retain integer, rational, or decimal kind. |
| `eo::is_neg` | 1 | Strict sign test on an arithmetic literal. |
| `eo::gt` | 2 | Strict numeric comparison; same kind required. Equal numeric values return false. |
| `eo::zdiv`, `eo::zmod` | 2 | Integers only, nonzero divisor. `a = b*q+r` and `0 <= r < abs(b)`. For `-7,-3`, quotient `3`, remainder `2`. |
| `eo::qdiv` | 2 | Same arithmetic kind, nonzero divisor; always returns a reduced RATIONAL, even for integer or decimal operands. |
| `eo::to_z` | 1 | Integer identity; rational/decimal floor, including negatives (`-7/3` becomes `-3`). |
| `eo::to_q` | 1 | Convert any arithmetic literal to reduced RATIONAL, retaining `/1` for integral values. |
| `eo::pow` | 2 | Arithmetic base; integer exponent in `[0,4294967295]`. Result retains base kind. `0^0=1`. Uses Stdlib `Zpower_alt` / `Qpower`. |
| `eo::log` | 2 | Integer base, arithmetic value. Floor the value, then compute the nonnegative floor logarithm; base <= 1 or value < 1 returns integer zero. |

Parsing consumes exactly one whole string. It accepts optional leading minus,
nonempty decimal digit integers, rational `numerator/denominator` with a
strictly positive digit denominator, and decimal `whole.fraction` with nonempty
parts; the pinned negative shorthand `-.digits` is also supported. Leading
zeroes are accepted. A leading plus, exponent notation, whitespace, extra
separators, trailing data, missing digits, or zero denominator fails. Negative
denominators are produced through arithmetic division, not accepted as literal
surface syntax. In particular, `1/0` is never zero and `1/2x` is never `1/2`.

Kind predicates reject malformed numeric-looking strings instead of treating
parse failure as false. This deliberately fails closed on unusual user symbol
names starting with digits or a minus followed by digits/dot, even when the
pinned lexer could treat some malformed negative-number spellings as symbols.
Ordinary variables such as `x` and object applications still answer false.
Upstream syntax validation is required for the other nonnumeric `Symbol`
strings, just as it is for ordinary symbol lookup.

## Reachability in the CPC signature

`Cpc.eo`'s recursive include closure contains 35 files. The arithmetic surface
below was inspected in that closure, not derived from rule-name guesses.
Line references are to the matching cvc5 1.4.2 `proofs/eo/cpc/` files.

| Helper path | Actual native calls and role |
| --- | --- |
| `Cpc.eo:137-202`, `$run_evaluate` | Equality first tests `is_q`/`is_z`; arithmetic comparisons use `is_neg`, `add`, `neg`, `to_q`; addition/multiplication/negation use their native counterparts; rational division uses `to_q`/`qdiv`; integer `div`, `mod`, and their `_total` branches use `zdiv`/`zmod`; `to_real`/`to_int` use `to_q`/`to_z`; `is_int` compares rational conversions. |
| `programs/PolyNorm.eo:31-185` | `$poly_neg` uses `neg`; `$poly_add` uses `add` on rational coefficients; `$mon_mul_mon` uses `mul`; `$get_arith_poly_norm_div` converts the denominator with `to_q`, tests `is_q` and nonzero, then computes `qdiv 1/1 denominator`; `$get_arith_poly_norm` converts constants with `to_q`/`is_q`. These rational coefficients are necessary even when the object formula is QF_LIA. |
| `rules/Arith.eo:245-277` | `$greatest_int_lt` and `$least_int_gt` use floor conversion, rational conversion, and integer `add` for strict integral bounds. |
| `programs/Arith.eo:9-10`, `rules/Arith.eo:328-352,398-409,584-589,629` | `$sgn` uses `is_neg` and `neg`; sign/coefficient and polynomial-relation helpers use `to_q` to compare zero/one or coefficient ratios. |
| `theories/Arith.eo:15,21`, `programs/Utils.eo:7` | `$is_numeral`, `$is_pos_numeral`, `$compare_geq` use numeric `gt`. |
| `programs/Arith.eo:30,39,48-51` | Integer log/pow/is-power-of-two helpers use `is_z`, `is_neg`, `log`, `pow`. This is signature coverage beyond the linear core, not a claim that exponentiation is a QF_LIA operator. |
| `programs/PolyNorm.eo:55-59` | `$poly_mod_coeffs` uses `to_z`, `zmod`, `to_q`. This is the BV coefficient path in the shared polynomial helper, not needed to assert linear integer polynomial coverage. |

The root rule `evaluate` (`Cpc.eo:432-434`) calls `$run_evaluate`
directly; `$evaluate` also reaches it via `$evaluate_list`
(`programs/Utils.eo:109`, `Cpc.eo:418-423`). `int_tight_ub` and
`int_tight_lb` (`rules/Arith.eo:264-289`) call the strict-bound helpers.
`arith_poly_norm` (`rules/Arith.eo:542-544`) compares the results of
`$get_arith_poly_norm` on both sides. These are concrete call edges; other
rule generation and signature elaboration requirements are separate.

Object-level zero-totalization is kept in the generated helper branches:
`Cpc.eo:182-194` explicitly handles zero denominators for `/_total`,
`div_total`, and `mod_total`. The native arithmetic module itself fails for
zero divisors. It does not duplicate or replace these signature programs.

`$poly_add` and `$mvar_mul_mvar` also call `$compare_var`, defined in
`programs/Utils.eo:171` as `(eo::cmp b a)`. **`eo::cmp` is deferred**:
the pinned implementation compares internal term hashes, not numbers or
lexicographic strings. Its ordering has not been established for this term
representation. Thus implementing numeric `gt` does not complete generated
polynomial normalization or generated LIA rule coverage.

## Unsupported and unfinished work

* `eo::cmp`/`eo::hash`, generic term ordering, and non-arithmetic primitives.
* Binary/hexadecimal overloads of arithmetic/comparison and `to_z`, and the
  single-character string conversion overload of `to_z`. Recognized numeric
  names fail on these operands; no alternate overload silently accepts them.
* Full expression evaluation and failure observations, type rules, parser
  normalization options, generated helper/rule coverage, and semantic gate
  integration. None are changed by these literal computations.
* General correctness proofs for the parser, serializer, rational operations,
  decimal normalization, and logarithm fuel bound are not supplied. Computation
  is kernel checked on the stated regression/differential corpus. The proved
  arithmetic interface facts are the Euclidean equation, remainder bounds and
  zero-divisor rejection. No object-level soundness lemma is claimed here.

## Reproduction and results

Use the private environment for every Rocq/dune command; dune jobs are capped
at two. These commands ran from the child worktree on 2026-11-03:

```sh
/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2 theories/checker/eunoia/EoArithmeticTests.vo
python3 tools/eunoia-arithmetic/check.py --out /tmp/eunoia-arithmetic-final
/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2 theories/checker/eunoia
/home/charles/code/friends/.toolchains/smtrocq-env rocq c -Q _build/default/theories/checker/eunoia SMTCoq.checker.eunoia /tmp/EoArithmeticAssumptions.v
```

All exited **0**. The static file has **133** compiled `vm_compute` examples,
covering valid/invalid tokens, all dividend/divisor signs, huge integers,
coefficient cancellation/reduction, kind/arity rejection, zero divisors,
conversion/floor, decimals, and power/log boundaries. `Print Assumptions` for
all five new general lemmas and Stdlib `Zpower_equiv` reports **Closed under the
global context** (six declarations). The explicit audit source/log are
`/tmp/EoArithmeticAssumptions.v` and `/tmp/eunoia-arithmetic-assumptions.log`.
The broader eunoia directory build also passed (exit **0**); its log is
`/tmp/eunoia-arithmetic-eunoia-build.log`.

The differential driver generated **1007** deterministic cases, using Python
`Fraction`/integer arithmetic as an additional independent expectation. It
recorded SHA256 hashes of the three prebuilt Rocq objects, then
compiled `/tmp/eunoia-arithmetic-final/Differential.v` in Rocq (exit **0**) and
checked corresponding value/kind or explicit failure observations against
pinned Ethos with `--no-normalize-dec` (exit **0**). This is a language literal
comparison, not solver acceptance evidence. Its `cases.json`, `rocq.log`,
`ethos.log`, and `report.json` retain the exact inputs, results, argv, exit
codes and reference binary SHA256. A separate changed-result control asserts
that `eo::add 1 2` is `4`; Ethos rejects it with expected subprocess return
**-6** (SIGABRT, with the intended type-mismatch diagnostic), verifying
that the differential harness observes the comparison. Core dumps are disabled
locally in the driver. Malformed-token tests live in the static
Rocq file; the differential inputs are lexically valid Eunoia expressions.

The private reference binary is
`/home/charles/code/friends/.toolchains/ethos-f97393e/ethos`. To reproduce its
build using existing private GMP headers/libraries, with no system install:

```sh
python3 tools/eunoia-arithmetic/build-reference.py
```

This records the complete g++ argv in the private `build.json` and compilation
output in `build.log`. This reproduction also exited **0**. The sources remain untouched. An initial differential
run was stopped (Rocq exit **-15**) after exposing linear-time `Z.pow` at the
maximum allowed exponent. The implementation now uses Stdlib's verified fast
`Zpower_alt`; the final corpus includes successful integer, rational and
decimal maximum-exponent cases. A redundant overlapping dune invocation was also stopped (dune exit **130**);
the driver now consumes the explicitly prebuilt objects instead of launching
another dune build. There are no skipped differential cases.
