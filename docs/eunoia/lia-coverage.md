# LIA CPC inventory and semantic certificate bridge

This is independent LIA groundwork, not an operational cvc5 backend. The CPC
files below were **produced, not checked**. No generated CPC rule evaluator,
parser-to-state binding, or tactic integration is supplied here. The verified
bridge checks an individual arithmetic implication against the existing SMTCoq
interpretation; it must be combined with the generated evaluator and core.

## Reproduction and scope

Inspected on 2026-11-03, from parent commit `2e1c1a7`, on child branch
`t3/eunoia-lia-coverage` (initial worktree branch `t3/21f5b285`). The private
tools used are:

```sh
TC=/home/charles/code/friends/.toolchains
CVC5="$TC/cvc5-1.4.2/cvc5-Linux-x86_64-static/bin/cvc5"
CPC="$TC/cvc5-1.4.2/cvc5-cvc5-1.4.2/proofs/eo/cpc/Cpc.eo"
python3 docs/eunoia/inspect_lia.py --cvc5 "$CVC5" --signature "$CPC" \
  --output /tmp/smtrocq-lia-audit
bash docs/eunoia/validate_lia.sh /tmp/smtrocq-lia-audit/validation
"$TC/smtrocq-env" dune runtest
```

The first command calls, for each input:

```sh
"$CVC5" --dump-proofs --proof-format=cpc INPUT.smt2
```

`inspect_lia.py` records exact argv, input/proof SHA256, solver exit status,
version, root/scope counts, and rule occurrences in
`/tmp/smtrocq-lia-audit/inventory.json`. It writes `.cpc` and `.stderr` files
beside the eleven explicit tactic transcriptions. Its regex counts are only
text inventory, never rule evaluation or proof acceptance. The solver reports
`cvc5 1.4.2 [git 282d5e0 on branch HEAD]`. The entry signature SHA256 is
`d13767eb873649c9f40482c99242c42081cf25308962f11c1981ce8e878770ad`;
this hashes `Cpc.eo`, not the entire include closure. Rocq reports 9.3.0,
compiled with OCaml 4.14.2. No dependency was installed for this work. Neither
Ethos nor Logos was used to validate these proofs or to establish the bridge.

All eighteen solver processes exited 0, printed `unsat`, and had empty stderr.
This says nothing by itself about their proof validity. Tactic samples are
manual SMT-LIB transcriptions of goals, **not runs of a new Rocq tactic**.

| Existing input | CPC steps, including `step-pop` | Main arithmetic behavior |
| --- | ---: | --- |
| `unit-tests/files/lia1.smt2` | 131 | branch reasoning, strict sum, negative scaling, integer upper tightening |
| `lia2.smt2` | 27 | normalize `x-3=7`, substitute `x=10`, evaluate |
| `lia3.smt2` | 28 | normalize `x>y` and `y+1<=x` to the same bound |
| `lia4.smt2` | 26 | Boolean equivalence between strict and shifted bounds |
| `lia5.smt2` | 110 | branch reasoning, negative scaling, sum contradiction |
| `lia6.smt2` | 30 | opposite bounds around `x-3`, normalize to `x>=10` |
| `lia7.smt2` | 27 | equality normalization and reversed `<=` |

These are the seven arithmetic goals also appearing in
`unit-tests/lfsc_tactics.v` around lines 563–600. Additionally, the script covers
the distinct integer goal shapes in that file's `Section LIA`, plus the integer
`ite`/parity and arithmetic-to-UF rewriting examples in `examples/Example.v`:

| Transcription filename stem | Goal shape, before negation | CPC steps |
| --- | --- | ---: |
| `tactic-refl` | `a=a /\ b=b` | 9 |
| `tactic-eq-symm` | `(a=b) = (b=a)` | 9 |
| `tactic-lt-plus1` | `a<b -> a<b+1` | 49 |
| `tactic-ge-trichotomy` | `x>=y -> y<x \/ x=y` | 43 |
| `tactic-uf-lia` | `f(a)>1 -> f(a)+1>=2 \/ f(a)=30` | 52 |
| `tactic-vacuous-eq` | `x=0 -> 8>=0` | 8 |
| `tactic-vacuous-lt` | `~(x<0) -> 8>=0` | 12 |
| `tactic-shift` | `a<b -> a+2<b+3` | 50 |
| `tactic-lt-plus10` | `a<b -> a<b+10` | 49 |
| `tactic-parity-ite` | nested Boolean `ite`, equalities between `2*x+i`, `i=0,1` | 131 |
| `tactic-uf-rewrite` | `x=y+1 -> f(y)=f(x-1)` | 31 |

Prop/Boolean variants and the repeated `a<b -> a<b+1` goal share a
transcription. This does not inventory every integer-containing example in the
repository (e.g. quantified group lemmas and arrays).

## Rules actually emitted

The seven files contain 379 steps and the eleven transcriptions 443. Counts
include repeated printing of a step inside different scopes; they are not
counts of globally unique step identifiers. Preserve hyphens versus underscores.

| CPC rule | Seven files | Eleven transcriptions | Existing semantic route, once exact step is bound |
| --- | ---: | ---: | --- |
| `arith_poly_norm` | 24 | 42 | Integer polynomial equality as a singleton LIA clause |
| `arith_poly_norm_rel` | 8 | 21 | Integer relation equivalence, with Boolean encoding caveat below |
| `arith_mult_neg` | 5 | 4 | Check its full sign-guarded implication, not just its consequent |
| `arith_sum_ub` | 4 | 4 | Check implication from exactly the listed premises to the generated sum bound |
| `int_tight_ub` | 2 | 0 | For integral `c`, `s<c -> s<=c-1` |
| `arith-elim-lt` | 11 | 16 | `(< a b) = not(>= a b)` |
| `arith-elim-gt` | 1 | 1 | `(> a b) = not(>= b a)` |
| `arith-elim-leq` | 4 | 1 | `(<= a b) = (>= b a)` |
| `arith-leq-norm` | 10 | 5 | `(<= a b) = not(>= a (b+1))` over integers |
| `arith-geq-tighten` | 0 | 1 | `not(>= a b) = (>= b (a+1))` over integers |
| `arith-eq-elim-int` | 0 | 4 | `(a=b) = ((a>=b) /\ (a<=b))` |
| `arith-int-eq-conflict` | 0 | 2 | **Unsupported mixed Real/Int intermediate formulas** |
| `arith-int-geq-tighten` | 0 | 1 | **Unsupported mixed Real/Int intermediate formulas** |

This table proposes reuse paths, not implemented CPC dispatch or verified
coverage of those rule names. The generated evaluator must determine which
rule instance is legal and its exact conclusion from the signature.

Other emitted rules in the seven files are:
`and_elim`, `and_intro`, `bool-double-not-elim`, `chain_m_resolution`,
`cnf_and_pos`, `cong`, `contra`, `eq-refl`, `eq_resolve`, `evaluate`,
`modus_ponens`, `nary_cong`, `not_and`, `not_implies_elim1`,
`not_implies_elim2`, `not_not_elim`, `not_or_elim`, `process_scope`, `refl`,
`reordering`, `scope`, `symm`, `trans`, `true_elim`.
The tactic transcriptions additionally emit `aci_norm`, `bool-impl-true1`,
`cnf_implies_neg1`, `cnf_implies_neg2`, `ite-else-false`, `ite-then-false`,
`ite_elim1`, and `ite_elim2`.

`lia1` and `lia5` each contain six `assume-push` commands and six `step-pop`
scope steps. Step IDs can be reused after popping a scope. Looking up a premise
in a single global ID map, dropping scope steps, or importing local hypotheses
as permanent roots would be unsound. The core must track these dependencies.

## Signature arithmetic programs

Paths here are relative to the matching `proofs/eo/cpc/` directory. The source
include closure, not this list, is the generator input.

* `Cpc.eo` includes `rules/Arith.eo` and `rules/Rewrites.eo`. Generic
  `evaluate` uses `$evaluate`, `$evaluate_internal`, `$evaluate_list`, and
  `$run_evaluate`; arithmetic constants are evaluated there, rather than by a
  solver assertion. Boolean `aci_norm` also occurs in integer examples.
* `rules/Arith.eo:18–78`: `$arith_rel_sum`, `$mk_arith_sum_ub_rec`,
  `$mk_arith_sum_ub` implement sum bounds. Input is a **nonempty** premise list
  packaged with `and`; it is reversed before accumulation from `(= 0 0)`.
  Allowed relation pairs are from `<`, `<=`, `=`. Any strict input makes the
  output strict; even `= + =` yields `<=`, not `=`. Operand/list order and the
  neutral element must be generated exactly.
* `rules/Arith.eo:86–160`: `$mk_arith_mult_pos`, `$arith_rel_inv`,
  `$mk_arith_mult_neg` compute multiplication conclusions. The rule conclusion
  itself is `((m>0 /\ F) -> F')` or `((m<0 /\ F) -> F')`. Multiplication by a
  negative coefficient reverses inequalities. A later `modus_ponens` supplies
  the guard; it cannot be silently absorbed into the rule.
* `rules/Arith.eo:170–242`: `$arith_rel_trichotomy`, `$arith_rel_neg`,
  `$arith_normalize_lit`, `$mk_arith_trichotomy` handle relation complements and
  trichotomy. The `arith_trichotomy` rule was not observed in this corpus.
* `rules/Arith.eo:249–291`: `$greatest_int_lt`, `$least_int_gt` use `eo::to_z`
  and `eo::to_q` for integral/rational constants. Only integral
  `int_tight_ub` instances were observed in the seven files. Negative fractional
  bounds require correct floor behavior, not OCaml truncation toward zero.
* `rules/Arith.eo:542–637`: `arith_poly_norm` requires identical
  `$get_arith_poly_norm` results. `arith_poly_norm_rel` additionally uses
  `$is_poly_norm_rel_consts_rel`, `$is_poly_norm_rel_consts`, and
  `$is_eq_maybe_to_real`: both scaling constants must be nonzero; inequalities
  require matching signs; equality does not require matching signs. The
  premise must have the specified scaled difference form (including a
  multiplicative list tail whose rational value is one). The checks must come
  from generation, even when another semantic certificate proves the result.
* `programs/PolyNorm.eo`: `$poly_neg`, `$poly_mod_coeffs`, `$poly_add`,
  `$mvar_mul_mvar`, `$mon_mul_mon`, `$poly_mul_mon`, `$poly_mul`,
  `$get_arith_poly_norm_div`, `$get_arith_poly_norm`,
  `$get_bv_poly_norm_rec`, `$get_bv_poly_norm`. Monomials are ordered term lists;
  coefficients are exact rationals. `$compare_var` in `programs/Utils.eo`
  controls ordering. Arithmetic normalization handles n-ary `+`, `*`, unary and
  binary `-`, constant division, and `to_real`; unsupported terms may become
  polynomial variables **inside the signature computation**, which does not
  authorize erasing their SMTCoq semantic meaning.
* `programs/Arith.eo` supplies `$sgn`, `$arith_mk_binary_minus`, and integer
  log/power helpers. `theories/Arith.eo` supplies `$arith_mk_zero` and the
  typed associative operators and neutral values. `rules/Rewrites.eo:64–118`
  contains the direct integer order/equality rewrites in the table.

The remainder of `rules/Arith.eo` also defines `$strip_even_exponent`,
`$mk_arith_mult_sign_sgn`, `$to_cube`, `$mk_arith_mult_abs_comparison_rec`,
`$mk_arith_mult_abs_comparison`, `$arith_to_int_reduction`,
`$arith_int_div_total_reduction`, `$arith_int_log2_reduction`, and
`$arith_reduction_pred`. Their rules `arith_mult_tangent`, `arith_mult_sign`,
`arith_mult_abs_comparison`, `arith_reduction` are unobserved here and are not
covered by this bridge. `arith_mult_pos`, `int_tight_lb` are also unobserved.

## Existing SMTCoq components and the bridge

The implementation in
[`EunoiaLia.v`](../../theories/checker/eunoia/EunoiaLia.v) adds no SMT-LIB
semantics and no CPC rule-name switch. It reuses:

* [`LIA.v`](../../theories/checker/small-checkers/lia/LIA.v):
  `build_clause`, `ZTautoChecker` through `check_micromega`, and
  `valid_check_micromega` over the existing `Atom`/`Form` tables and valuation.
  `build_op2` admits integer equality and `<`, `<=`, `>=`, `>`; term reification
  understands integer constants, addition, subtraction, multiplication, and
  negation. Other integer terms can remain shared opaque variables.
* [`EUF.v`](../../theories/checker/small-checkers/euf/EUF.v):
  `check_trans`, `check_congr`, `check_congr_pred` and their validity lemmas for
  typed term equalities/congruence, also useful for arithmetic operators and
  applications such as `f(x-1)`. These return theory clauses with negated
  equality premises, not an unchecked conclusion. Boolean formula congruence
  and n-ary-to-binary translation also need the existing Boolean/syntactic
  checkers; not every CPC `cong` is one call to EUF.
* [`Arithmetic.v`](../../theories/checker/small-checkers/spl/Arithmetic.v):
  `check_spl_arith t_form t_atom orig res cert` handles a **singleton** premise
  clause by checking `[not premise; res]`; `valid_check_spl_arith` also requires
  validity of `orig`. It is not a multiple-premise sum checker.
  [`Syntactic.v`](../../theories/checker/small-checkers/spl/Syntactic.v)
  recognizes some syntactic identities (including operand symmetry), not
  general integer polynomial normalization.

`LIA.check_micromega` returns the requested clause on success and `C._true` on
failure. Its result is always valid. Thus "the returned clause is valid" is
**not** evidence that the requested CPC conclusion was checked. `check_clause`
instead exposes a Boolean failure: it runs the same `build_clause` and
`ZTautoChecker`, returning false if reification or the certificate fails.
`check_clause_result` proves that acceptance returns the exact requested
clause from the existing checker. `check_clause_sound` obtains semantic validity
directly from `LIA.valid_check_micromega`, with the existing table well-formedness
and typing premises explicit in the theorem.

`check_step` forms exactly:

```text
step_clause [p1; ...; pn] q = [not p1; ...; not pn; q]
```

`check_step_sound` proves that successful checking and truth of **all** the
specified premise literals imply truth of the specified conclusion literal.
Premises are formula literals, not clauses to be flattened into independent
facts: a disjunctive premise needs a `Form.For` literal for the whole formula.
No `State` mutation or scope handling is added here. The core owner can use this
lemma when preserving the existing `S.valid` invariant after checked lookup
and scope discharge. A local `false` under assumptions must become a discharged
clause, not an unconditional empty clause.

For example, `lia1.cpc` has:

```text
(step @p70 :rule int_tight_ub :premises (@p69))
(step @p71 :rule arith_mult_neg :args (-1 @t20))
...
(step @p79 :rule arith_sum_ub :premises (@p78 @p75 @p70))
```

Here `@p69` is `x<4`, `@p70` is `x<=3`, and the sum combines `y<8`,
`-1*(x+y)<=-1*11`, and `x<=3`. The generated conclusion uses the unreduced sum
on both sides; separate CPC normalization/evaluation steps reduce it to a
contradiction. Checking only the simplified end inequality would omit those
steps and would not validate this CPC derivation.

## OCaml certificate production and normalization requirements

[`src/lia/lia.mli`](../../src/lia/lia.mli) already exposes:

```ocaml
val build_lia_certif :
  SmtAtom.Form.t list ->
  RocqInterface.Micromega_plugin_Certificate.Mc.zArithProof list option
```

The list is a **clause**, not a conjunction of facts. For an individual CPC
step, call it on `List.map Form.neg premises @ [conclusion]`, after all terms
are reified into the same tables. `lia.ml` negates the clause, converts it to
Micromega, obtains the CNF obligations with `cnfZ`, and calls the OCaml Lia
certificate producer for each obligation. `Some cert` remains untrusted until
the Rocq Boolean gate checks it. Fail closed on `None` or any unsupported
conversion exception. The new bridge does not call this OCaml API yet.
`src/verit/syntax.ml:153–177` demonstrates existing certificate production for
`LiaMicromega` and `SplArith`; its legacy fallback to `ImmFlatten` is not
authorization to skip an unsupported CPC rule.

Concrete constraints for integration:

1. Encode numerals with the existing binary positive/`Z` atom constructors,
   including zero and negative numbers; do not store arbitrary coefficients
   in machine integers. Table IDs use Uint63; arithmetic coefficients use `Z`.
   Preserve hash-consing/shared opaque integer terms across premises and result.
2. Translate n-ary arithmetic into existing binary operators with certified
   preservation of order, associativity, and empty/singleton neutral behavior.
   CPC prints e.g. `-3` and `(+ 8 (* -1 11) 3)`; source SMT-LIB also uses unary
   `(- 3)`. Treat unary negation and subtraction distinctly.
3. Preserve strictness and polarity. Integer `s<c` tightens to `s<=c-1`,
   whereas `s<=c` does not. A negative scaling flips the direction; a zero
   coefficient is disallowed by `arith_poly_norm_rel` even if a semantic
   certificate happens to prove a particular instance.
4. The Rocq `LIA.build_hform` supports `Fiff`, `Fxor`, and `Fite`, but the
   **OCaml** converter currently raises `todo:Fiff`, `todo:Fxor`, and
   `todo:Fite`. CPC Boolean equality should use existing `Form.Fiff`, not
   `Atom.BO_eq Typ.TZ`, and will therefore need a producer extension or
   certified Boolean decomposition into exact per-step obligations. Do not
   confuse a verified Rocq reifier with an implemented OCaml producer path.
5. Polynomial normalization can require products beyond syntactic LIA.
   The Rocq reifier supports `PEmul`, but `Certificate.lia` is not a complete
   nonlinear arithmetic producer. Its failure must reject the step; no global
   fallback solver is supplied here.

## Unsupported intermediate rationals, even for QF_LIA

The `examples/Example.v` parity transcription is a concrete blocker to claiming
integer example coverage. Its CPC trace defines:

```text
@t17 = (+ x1 (* -1 x2))
@t30 = (to_int 1/2)
@t31 = (to_real @t17)
@t32 = (* -1/1 (- @t31 1/2))
```

It then uses `arith_poly_norm` with `-1/2`, `arith_poly_norm_rel` over mixed
Int/Real formulas, `arith-int-geq-tighten` at step `@p22`, and
`arith-int-eq-conflict` at `@p66` and `@p79` (also using `-1/2`). Exact rational
normalization in the signature is necessary but is not a proof of the Real
formula under the existing SMTCoq interpretation: the present `Typ` has no
arithmetic Real semantics. Mapping these terms to arbitrary integers, dropping
coercions, or rounding coefficients is unsound.

This work deliberately rejects that boundary. A future, separately verified
translation to existing integer obligations would need positive denominator
clearing, sign preservation, integer floor/ceiling facts (including negative
fractions), and a proof connecting **each exact mixed-sort CPC step** to its
integer obligation. No such translation is claimed here. Choosing a cvc5 proof
configuration that avoids these steps would also require new measured traces;
none was tested. Division/modulo/abs, nonlinear and transcendental rules,
arithmetic/bitvector conversions, and general Real arithmetic remain outside
the observed/verified path.

## Validation and negative checks

`validate_lia.sh` compiles the new files into the selected `/tmp` directory
using explicit `-Q` mappings to `_build/default/theories/{utils,structures}`,
`checker/fol`, `checker/small-checkers/{euf,lia}`, and the temporary eunoia
directory. It calls `rocq c` on both files and on a baseline assumption audit,
then `rocq check SMTCoq.checker.eunoia.EunoiaLiaTests`. The existing dependencies
are built first with `smtrocq-env dune build theories`. No dune or tactic file
was changed. This matters: the current `dune build`/`runtest` **does not register
or automatically test** the new eunoia files.

The bridge's four lemma audits use `Print Assumptions`. The soundness lemmas
inherit Uint63 primitives/specifications and
`ProofIrrelevance.proof_irrelevance` from the existing LIA soundness proof;
they are not claimed closed under the global context. The validation script
compares each reported dependency set against
`LIA.valid_check_micromega` with matching imports and verifies that no additional
dependency is introduced. There are no new assumptions or proof holes.

Recorded validation results (all through the private wrapper for Rocq/dune):

| Command | Exit/result | Log path below `/tmp/smtrocq-lia-audit/` |
| --- | --- | --- |
| `python3 docs/eunoia/inspect_lia.py ...` as above | 0; eighteen CPC text samples | `inventory.json`, `*.cpc`, `*.stderr` |
| `dune build theories` | 0; existing theory build | `validation/dune-build.log` |
| `rocq c ... EunoiaLia.v` inside `validate_lia.sh` | 0; four assumption reports | `validation/EunoiaLia.log` |
| `rocq c ... EunoiaLiaTests.v` inside the script | 0; 13 computation examples | `validation/EunoiaLiaTests.log` |
| baseline audit and dependency comparison | 0; no added dependencies | `validation/LiaBaselineAssumptions.log` |
| `rocq check ... SMTCoq.checker.eunoia.EunoiaLiaTests` | 0; `Modules were successfully checked` | `validation/kernel-check.log` |
| `dune runtest` | 0; existing suite, with existing warnings | `dune-runtest.log` |

[`EunoiaLiaTests.v`](../../theories/checker/eunoia/EunoiaLiaTests.v) checks 13
examples with kernel-checked computation:

* Positive: `x=x`; `x<=0 -> x<=1`; `x<=0 -> 2*x<=0` with an explicit
  `ZArithProof` certificate.
* Negative: strengthened conclusion `2*x<0`; omitted certificate; certificate
  coefficient changed from 2 to 3; missing premise; changed premise `x<=1`;
  reversed implication `x<=1 -> x<=0`; unsupported Boolean atom; equality of
  unsupported type; empty clause.
* Fallback check: the existing checker returns `C._true` for an empty clause
  with no certificate, while the Boolean gate rejects it.

The tests exercise the certificate gate, not a CPC parser, generated rule
side conditions, table typing checks, or scope/ID lookup. Deliberately
unsupported atoms are included only to test rejection; the tests do not assert
that their whole table is well typed. The soundness theorem still requires the
actual typing/well-formedness hypotheses. Corrupted CPC rule names, roots,
scope pops, and premise IDs cannot yet be tested end to end with this module.

## Required coordinator interfaces and remaining work

* Generator: typed, fail-closed rule evaluation from the full signature include
  closure, including helper programs and side conditions. Return the exact
  computed conclusion and ordered premise binding; never replace generation
  with the rule inventory above.
* Core: checked source-to-`Atom`/`Form` translation, explicit root binding,
  scoped proof identifiers, premise existence and accessibility checks, and a
  proof connecting the step's formula literals to its semantic gate. Validate
  `Atom.check_atom`, `Form.check_form`, `Atom.wt`; propagate actual acceptance
  rather than silently replacing a failed step with a true clause.
* Certificate producer: one untrusted `ZArithProof list` per exact arithmetic
  step obligation, using the same atom/form tables. Extend or decompose the
  OCaml Boolean cases before claiming equivalence/`ite` coverage. Add complete
  CPC mutation tests when the parser/core exists.
* Build owner: register `EunoiaLia.v` and the test in the coordinator's eunoia
  theory/stanzas, with dependencies on `Stdlib`, `SMTCoq.utils`,
  `SMTCoq.structures`, `SMTCoq.checker.fol`, and
  `SMTCoq.checker.small_checker.lia` (and EUF as required by the common theory).
  The standalone validation script supplies a working compile path meanwhile.
* Mixed-rational arithmetic, per-rule semantic certificates on actual CPC
  traces, and the cvc5 tactic itself remain incomplete.

Producing a fresh Lia certificate for **each exact CPC step**, after signature
evaluation, is local proof reconstruction with a verified semantic gate.
Re-running `lia`/another solver on the original goal and ignoring the CPC trace
would independently reprove the goal; it would not check the cvc5 proof.
No end-to-end CPC acceptance or overall port completion is claimed.
