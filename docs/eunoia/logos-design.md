# Logos / Eunoia design for the cvc5 port

Design survey, 2026-11-03. This report proposes interfaces and proof obligations;
it does not implement a backend or establish QF_UF/QF_LIA coverage. It follows
[implementation-plan.md](implementation-plan.md), [BEST_PRACTICE.md](../../BEST_PRACTICE.md),
and [ARCHITECTURE.md](../../ARCHITECTURE.md). No shared dune or tactic file is
changed, and no Rocq lemma or assumption is added.

Recommended first implementation: compile the pinned CPC source into executable
rule/program data, interpret that data with a bounded, fail-closed evaluator in
Rocq, and require a separate verified semantic certificate for **every** derived
step. Interpret supported EO terms through existing SMTCoq `Typ`, `Atom`, `Form`,
`Lit`, and `C`; store checked clauses in existing `S.t`. Use Ethos desugaring as
a reference and a possible alternative frontend to the same evaluator interface.
Neither a rule-name inventory nor a hand-written CPC rule switch constitutes
signature compilation. A compiler/evaluator success is not semantic evidence.

## Sources and pins

All source inspections used the following local, unmodified references. Git
status was empty in both reference repositories before and after inspection.

| Source | Version and local location | Pinned upstream entrypoint |
| --- | --- | --- |
| SMTCoq child checkout | Initial branch `t3/02e7a2ee`, renamed during the survey to `t3/document-eunoia-design`; starting commit `2e1c1a7e1c1c8c24dccef330675789371a13ee1d` | Local implementation plan and checker sources |
| Logos | `89df5909b0e9aabb936b68ee95c75a18f609db7a`, `/tmp/smtrocq-logos` | [README](https://github.com/cvc5/logos/blob/89df5909b0e9aabb936b68ee95c75a18f609db7a/README.md), [installer](https://github.com/cvc5/logos/blob/89df5909b0e9aabb936b68ee95c75a18f609db7a/install/install-sig.sh) |
| Ethos / Eunoia compiler | `f97393ea55f03653689e104d0e9c9010ee17780c`, `/tmp/smtrocq-ethos`; this is also Logos's `ETHOS_VERSION` pin | [compiler README](https://github.com/cvc5/ethos/blob/f97393ea55f03653689e104d0e9c9010ee17780c/tools/eoc/README.md), [design](https://github.com/cvc5/ethos/blob/f97393ea55f03653689e104d0e9c9010ee17780c/tools/eoc/docs/design.md), [driver](https://github.com/cvc5/ethos/blob/f97393ea55f03653689e104d0e9c9010ee17780c/tools/eoc/driver.py) |
| cvc5 and CPC | Tag `cvc5-1.4.2` resolves through GitHub's refs API to commit `282d5e0c84baf49c780704c532f87ba66d8b513d`; binary reports `1.4.2 [git 282d5e0 on branch HEAD]` | [matching Cpc.eo](https://github.com/cvc5/cvc5/blob/282d5e0c84baf49c780704c532f87ba66d8b513d/proofs/eo/cpc/Cpc.eo) |

In the commands below, `TC=/home/charles/code/friends/.toolchains`,
`CVC=$TC/cvc5-1.4.2/cvc5-Linux-x86_64-static/bin/cvc5`,
`CPC=$TC/cvc5-1.4.2/cvc5-cvc5-1.4.2/proofs/eo/cpc`, and
`EVID=/tmp/smtrocq-logos-design-evidence`. These are task-specific variables,
not changes to the shell environment configuration. The local signature's
`Cpc.eo` SHA-256 is
`d13767eb873649c9f40482c99242c42081cf25308962f11c1981ce8e878770ad`.
Its recursively included closure contains 35 files and 609 `declare-rule`
forms with 609 distinct names, including the unsound `trust` declaration.
These counts are an inventory, not supported-rule counts.

## Issue #485: read before the source survey

The [issue body](https://github.com/cvc5/logos/issues/485), opened 2026-10-23,
asks whether signature generation inherently causes Logos's performance gap.
The web rendering omitted replies, but fetching the public comments API
returned **two** comments, matching the issue API's comment count. Both are by
`ajreynol`, dated 2026-10-30:

* [18:41:48 UTC, comment 6530772316](https://github.com/cvc5/logos/issues/485#issuecomment-6530772316): earlier measurements put Logos roughly 4–5 times slower than Ethos on average. The reply identifies missing memoization of side-condition computations, specialization of list primitives, and term-hashing improvements. It also mentions possible further improvements from custom rule checking routines and describes the simple, provable definition as a basis for future efficient checkers.
* [18:44:37 UTC, comment 6530824091](https://github.com/cvc5/logos/issues/485#issuecomment-6530824091): the maintainer offers help with Rocq port design discussions.

This corrects the initial observation in the implementation plan that the web
rendering showed no maintainer reply. The reported factor is a historical
measurement without a benchmark corpus or configuration in that comment. It
does not predict this Rocq port's speed or compare it with Lean-SMT or
Sledgehammer. The optimization recommendations below are design inferences,
not measured improvements. No comment or other message was sent upstream.

## What Logos generates, and what needs proofs

The [installation script](https://github.com/cvc5/logos/blob/89df5909b0e9aabb936b68ee95c75a18f609db7a/install/install-sig.sh)
and generated banners make the boundary concrete:

| Portion | Generation / proof responsibility | Rocq consequence |
| --- | --- | --- |
| `Cpc/LogosTerm.lean` | Generated `UserOp`, EO `Term`, and associated syntax | Generate symbols, operator attributes and syntax from the signature; EO syntax is not a second SMT-LIB model. |
| `Cpc/Logos.lean` | Generated helpers, rule programs, rule tags, commands, state operations, dispatcher and executable refutation test | Generate executable bodies and guards, preserving argument/premise order, failures and rule attributes. |
| `Cpc/SmtModel.lean`, `SmtEval.lean`, `Spec.lean`, native support | Signature-wide output is produced using compiler templates plus `.eos` semantic configuration; `Spec` translates EO terms to the model | Do not copy this model into Rocq. Supply a bridge to SMTCoq's existing interpretation instead. Generated configuration is still something whose meaning requires justification. |
| `Cpc/Proofs/Rules/*.lean` | Compiler emits rule statements; installer preserves existing, human-developed proof bodies | A generated obligation is not a discharged obligation. Emit a manifest of outstanding obligations, never proof-hole files in the accepted Rocq build. |
| `Cpc/Proofs/RuleLemmas.lean` | Generated dispatcher assembles per-rule correctness facts | A dispatcher may reference only proved bridges, or require checked per-step semantic certificates. Missing support rejects the step. |
| `Proofs/CheckerCore.lean`, `CheckerState.lean`, `Checker.lean`, translation/support proofs | Maintained proofs for interpretation, state invariants, scope discharge and final refutation | Reuse SMTCoq's state/trace infrastructure and prove the EO adapter's preservation and refutation results. |
| `Api.lean`, `ApiChecks.lean`, `ApiCorrect.lean` | Maintained executable connection and proofs of runtime checks | Bind the checked proof to the original reified roots; executable output alone does not prove that binding. |

For example, `Logos.lean` has `__mk_trans`, `__eo_prog_trans`, and a dispatcher
arm passing the conjunction of referenced premises to that program. In
`Proofs/Rules/Trans.lean`, separate proofs establish the meaning of the returned
equality. The core then combines per-rule properties into its state invariant.
Its `correct___eo_is_refutation` theorem requires
`TranslatableAssumptionList` and `CmdListTranslationOk`. Logos's API checks
those conditions and reports an incomplete result if translation is outside
its model. The correctness claim is relative to parsed assumptions; the
README explicitly says those assumptions are not compared with an original
input problem. The parser documentation also says `include` and `reference`
commands are ignored. This port needs a stronger root-binding boundary.

Do not blindly port the generated stack's defaults: Logos's
`__eo_state_proven_nth` returns Boolean true when lookup runs out of entries.
Require an explicitly live, bound premise in the proposed adapter. Likewise,
the generated file contains a raw `__eo_prog_trust`, but that does not make
it an accepted sound rule: Ethos's `Desugar::finalizeRule` returns early for
rules marked `:sorry`, and unsupported dispatcher cases yield `Stuck`. The
Rocq compiler must record rejected declarations and the runtime must reject
any `trust` use, even in an unused portion of a purported proof.

This survey did not build Logos's Lean proofs. The README distinguishes its
representative/stubbed CI checks from the full per-rule proof build; neither
source inspection nor generation is a new verification of those proofs.

## Actual UF / LIA source constructs

The following are observations of the matching **cvc5 1.4.2** signature, not
an assumption that Logos's cached signature is byte-identical to it. Paths in
this section are relative to `$CPC`. The pinned
[UF rules](https://github.com/cvc5/cvc5/blob/282d5e0c84baf49c780704c532f87ba66d8b513d/proofs/eo/cpc/rules/Uf.eo),
[arithmetic rules](https://github.com/cvc5/cvc5/blob/282d5e0c84baf49c780704c532f87ba66d8b513d/proofs/eo/cpc/rules/Arith.eo),
and [polynomial programs](https://github.com/cvc5/cvc5/blob/282d5e0c84baf49c780704c532f87ba66d8b513d/proofs/eo/cpc/programs/PolyNorm.eo)
are particularly relevant.

### Declaration and evaluator requirements

Includes resolve relative to each including file, with shared includes appearing
only once in the dependency inventory. Terms include typed parameters,
implicit type arguments, overloaded symbols such as unary/binary `-`, curried
application and the explicit `_` application form. `program` contains ordered
pattern cases; repeated pattern variables impose syntactic equality, and a
failed case can continue to a later case. `define` and `eo::define` introduce
macros/local bindings. Preserve source scoping rather than textual substitution
that can capture names. Pattern variables marked `:list` denote an operator's
variadic tail, not one ordinary scalar argument.

`theories/Builtin.eo` gives `and` and `or` right-associative nils `true` and
`false`. `theories/Arith.eo` gives `+` and `*` type-dependent right-associative
nils via `$arith_mk_zero` and `$arith_mk_one`. The arithmetic signature permits
mixed Int/Real operations. Never infer an Int-only fragment merely from
the rule's name or from a source type variable `T`.

Required program primitives include syntactic `eo::eq`, guarded
`eo::requires`, conditionals, integer/rational operations and conversions,
`eo::typeof`, `eo::cmp`, and operator-aware `eo::list_*` operations. Syntactic
`eo::eq` and the object-level equality symbol `=` have different roles.
`eo::requires` must not succeed just because both failed computations have
the same error sentinel: Logos's generated `__eo_requires` expressly checks
that the equal values are not `Stuck`. Do not coerce errors into Boolean false,
zero, or an unchanged term. Evaluation must respect the control behavior of
conditionals and guards; a failure in an unselected branch must not change a
successful result.

### Rule and program examples

| Rule / source | Actual construction | Implication for the port |
| --- | --- | --- |
| `refl`, `rules/Uf.eo:11` | No premises, argument `t`, conclusion `(= t t)` | A typed equality reflexivity bridge is sufficient. |
| `eq-refl`, `rules/Rewrites.eo:3347` | Argument `t1`, conclusion `(= (= t1 t1) true)` | This is a different rule from `refl`; Boolean equality must bridge to `Form.Fiff`. |
| `symm`, `rules/Uf.eo:21` | `$mk_symm` matches equality or negated equality and reverses operands | Preserve both cases; EUF symmetry alone does not cover all Boolean wrappers. |
| `trans`, `rules/Uf.eo:49` | `:premise-list` gathers an ordered `and` chain; `$mk_trans` uses `eo::requires` to join exact endpoints, terminating at `true` | Generated syntactic joining must run even if the semantic EUF checker accepts a more permissive orientation. |
| `cong`, `rules/Uf.eo:79` | Reverses the premise conjunction, recursively traverses a curried application spine, checks repeated variables, rebuilds the RHS using `_` | Flattening to `Atom.Aapp` needs saturated first-order applications; Boolean operators need a propositional bridge. |
| `nary_cong`, `rules/Uf.eo:116` | Separate program processes the typed `:list` tail and has a remaining-tail case when the premise conjunction is `true` | Ordinary `cong` cannot silently replace it. Preserve list elaboration and source case order. |
| `and_elim`, `eq_resolve`, `rules/Booleans.eo` | Selection from a Boolean conjunction and transport along a Boolean equivalence | These are required even by the supplied UF fixture. Check selection bounds and exact premise polarity. |
| `arith_sum_ub`, `rules/Arith.eo:18` | `$mk_arith_sum_ub` reverses the premise list, seeds a type-specific `(= zero zero)`, and folds `$arith_rel_sum` | The relation-combination table is executable signature data. In particular its `=, =` case returns `<=`, not `=`. |
| `arith_mult_pos`, `arith_mult_neg`, `rules/Arith.eo:86,139` | Construct implications with sign and arithmetic-atom hypotheses; negative multiplication reverses relation via `$arith_rel_inv` | These are not arbitrary multiplication steps with an assumed sign. Certify the entire generated implication. Start with literal integer multipliers. |
| `arith_trichotomy`, `rules/Arith.eo:237` | Normalizes two negated input literals, then invokes `$mk_arith_trichotomy` | Preserve normalization and both premises, rather than treating the rule tag as a generic ordering tautology. |
| `int_tight_ub`, `int_tight_lb`, `rules/Arith.eo:249,274` | `$greatest_int_lt` uses `eo::to_z`, rational conversion/equality and a conditional decrement; `$least_int_gt` uses `1 + eo::to_z` | For literal integer bounds, these reduce to `k-1` and `k+1`. General rational bounds require exact conversion semantics; reject them in an Int-only object fragment. |
| `arith_poly_norm`, `rules/Arith.eo:542` | `:requires` compares `$get_arith_poly_norm` of both sides of the supplied equality | Execute the source normalization before the semantic check; a coefficient list or rule inventory alone is insufficient. |
| `arith_poly_norm_rel`, `rules/Arith.eo:623` | A premise equates scaled differences; guards require nonzero factors, compatible signs for inequalities, unit tail, and matching differences (possibly through `to_real`) | Keep these exact guards. Initially reject object-level Real/coercion cases until a bridge exists. |
| `evaluate`, `Cpc.eo` | `$run_evaluate` recursively computes constants and operator cases, with a final identity case | Generate its cases, including the fallback; do not turn an unsupported known branch into that fallback. Boolean and integer cases need their own coverage. |
| `scope`, `process_scope`, `rules/Builtin.eo` | `scope` has `:assumption F` and a premise `G`, deriving `F => G` via `step-pop`; helpers collect nested antecedents for `process_scope` | A proof containing scopes needs a discharge invariant, not unrestricted insertion of local assumptions into `S.t`. |
| `chain_m_resolution`, `rules/Booleans.eo:233` | Explicit result `Cr`, polarity and pivot lists; computes a resolvent, converts to a set, then checks equality or `eo::list_minclude` | List length, multiplicity and inclusion direction matter. This is an immediate use for the list optimizations mentioned in #485. |

`programs/PolyNorm.eo` declares internal monomial/polynomial constructors,
with monomials represented by ordered EO-term lists and rational coefficients.
`$poly_add` merges ordered polynomials and cancels zero coefficients;
`$mvar_mul_mvar`, `$mon_mul_mon`, `$poly_mul_mon`, and `$poly_mul` implement
products. `$get_arith_poly_norm` handles negation, variadic addition and
multiplication, subtraction, division by a nonzero rational constant, and
`to_real`. Other terms can become atomic variables in the normal form.
`programs/Utils.eo` defines `$compare_var a b` using `eo::cmp b a`.

An Int-only **object** fragment still needs rational **meta-computation** for
this helper. Those exact coefficients do not justify adding a Real model to
SMTCoq. Restrict object multiplication to a supported linear form (constant
scaling); reject products of two variable-dependent integer expressions in
the initial LIA profile. Internal polynomial constructors need operational
meaning, but must not appear untranslated in premises or conclusions.

### Observed proof surface

The fresh `uf4` dump is byte-identical to `/tmp/smtrocq-uf4.cpc`: 15 steps,
with `and_elim` (3), `cong` (6), `eq-refl` (1), `eq_resolve` (2), `evaluate`
(1), and `trans` (2). For example, it uses `cong` on a negated equality and
on equality predicates. Those cannot all be passed directly to
`EUF.check_congr`, whose object equality cases inspect `Atom` nodes.

The fresh `lia1` dump has 131 steps and 27 distinct rule names (full counts in
the command evidence below). It also has six `assume-push` commands, six
`step-pop :rule scope` steps, two `process_scope` steps, and repeated printed
step names such as `@p70` in distinct scoped portions. Allocate internal IDs
from command occurrences with scoped name resolution; printed numeric suffixes
are not safe array indices. A declared QF_LIA problem does not imply a
scope-free proof. Both dumps are **unverified solver output** here; their
`unsat` lines are not a port acceptance result.

## Source compilation versus Ethos desugaring

The pinned compiler supports Lean, SMT VC/SyGuS, and desugared Eunoia output;
it has no Rocq backend. Its ordinary Lean path is
`desugar -> model-smt -> lean-meta` (with trimming in selected-rule runs).
The `model-smt` stage imports a separate SMT model. This port should stop
before that stage and target existing SMTCoq semantics.

| Approach | Benefits | Costs / trust boundary | Suggested use |
| --- | --- | --- | --- |
| Direct CPC source to Rocq program IR | Records exact `.eo` provenance and guards; no model-generation stage; can reject unimplemented source forms early | Must implement Eunoia elaboration, macros, overloads, list attributes, ordered nonlinear patterns and primitive behavior. A shallow s-expression scan is insufficient. | Initial bounded subset, with generated executable programs and explicit coverage errors. |
| Ethos `desugar --natives embed` to the same IR | Reuses Ethos parser/elaborator and pattern linearization; native operations have explicit names and signatures | Larger embedded term vocabulary; every reached `$native_*` needs a checked Rocq implementation; upstream translator is not a verified equivalence with Ethos | Alternative frontend after closure/coverage audit; useful reference for direct lowering. |
| Ethos `desugar --natives eo` to the same IR | Expands natives back to designated Eunoia primitives, reducing the backend's native mapping surface | More generated code and recursion; still requires exact primitive semantics and a compiler audit | Evaluate against the same fixtures before choosing it over `embed`. |
| Port emitted Lean text or take a successful SMT VC result | Existing obligations can guide proof statements | Lean-specific recursion/native/semantic layers; emitted obligations and solver results are not Rocq proofs | Do not use as an acceptance path. |

The [desugar implementation](https://github.com/cvc5/ethos/blob/f97393ea55f03653689e104d0e9c9010ee17780c/plugins/desugar/desugar.cpp)
linearizes repeated pattern variables into explicit tests and fallback helpers;
the generated `__mk_cong_rhs` in Logos shows this concretely. Preserve that
fallback behavior in either frontend. The
[checker emitter](https://github.com/cvc5/ethos/blob/f97393ea55f03653689e104d0e9c9010ee17780c/plugins/desugar/desugar_checker.cpp)
derives dispatcher arities from the rule program, and gathers `:premise-list`
using its declared operator/nil. At this pin it limits ordinary rule arguments
to ten and fixed premises to eight; a frontend must propagate such errors,
not truncate arguments.

Other documented Ethos limits matter: non-ground nil predicates supplied by
configuration are not automatically proved correct; generated `$eo_typeof`
approximates the original type system; exclusions are literal names without
dependency closure; full native coverage is not automatically established.
Different `--final-out-dir` values do not isolate concurrent runs because
generated configuration and plugin artifacts share locations. Use a dedicated
writable copy and serialize compiler runs. Do not run the installer against
the read-only `/tmp` references. Any future toolchain copy/build must live
under `$TC` in this task's dependency policy.

The `desugar --help` command was executed, but no `ethos-eoc` build or actual
desugaring was performed in this job. A future experiment, **not executed**,
would use a pinned writable source copy at `$TC/ethos-eoc-f97393e`, build its
`plugins` project with CMake, then invoke that copy's `tools/eoc/driver.py
desugar --build-dir <private-build> --final-out-dir <private-output>
--semantics <pinned-Cpc.eos> --natives embed <matching-Cpc.eo>`, and repeat
with `--natives eo`. Even this desugar command compiles configuration sets:
merely changing its output directory does not make the source copy read-only.

For the direct route, use the same normalized rule/program IR for all rule
bodies. Record the entire include manifest, selected rule dependency closure,
declaration attributes, source spans and rejected constructs. Preserve every
case in a selected program. If its syntax cannot be represented, fail that
compilation; if syntax is represented but an evaluation primitive is outside
the declared runtime profile, evaluating that branch must fail explicitly.
Never delete an unsupported case and let execution fall through to another.
Generating only an allowlist of tags does not meet the integration contract.

An unverified frontend can remain outside semantic trust if a Rocq-checked
semantic gate validates every derived fact. That does not prove the frontend
faithfully implements Eunoia or that an accepted trace is the exact CPC
derivation. Track that separate obligation with generated-source snapshots,
mutation tests and Ethos differential tests, and eventually a translation
correctness argument. These checks supplement, not replace, the semantic gate.

## Semantic bridge: use the existing interpretation

Relevant existing paths are [Terms.v](../../theories/checker/fol/Terms.v),
[State.v](../../theories/checker/fol/State.v),
[EUF.v](../../theories/checker/small-checkers/euf/EUF.v),
[LIA.v](../../theories/checker/small-checkers/lia/LIA.v), and
[MainChecker.v](../../theories/checker/MainChecker.v).

| Supported EO object | Existing representation / proof obligation |
| --- | --- |
| `Int`, Boolean, declared uninterpreted sort | `Typ.TZ`, `Typ.Tbool`, `Typ.Tindex`; use the existing `CompDec`/interpretation tables. Do not impose infinite uninterpreted domains. |
| Integer literals, `+`, unary/binary `-`, constant multiplication, comparisons | Existing `Atom` constants/unary operators and `BO_Zplus`, `BO_Zminus`, `BO_Zmult`, `BO_Zlt/le/ge/gt`. Expand variadic forms with a proved fold bridge. |
| Saturated first-order uninterpreted application | `Atom.Aapp` with the existing function table and checked argument/result types; reject partial applications as object terms. |
| Equality | Non-Boolean operands use `Atom.BO_eq`; Boolean equality uses `Form.Fiff`, with a bridge to the same Boolean truth condition. |
| Boolean connectives, negation, `ite` | Existing `Form` nodes and `Lit.neg`; term-valued `ite` needs an existing encoding/proved bridge or rejection. |
| Proof fact / disjunction | A singleton literal clause or a justified clause view in `C.t`; clauses are interpreted by `C.interp`, with state validity `S.valid`. |

The valuation is the existing
`Form.interp_state_var (Atom.interp_form_hatom ...) (Atom.interp_form_hatom_bv ...) t_form`.
The checker must require `Form.check_form`, `Atom.check_atom`, and `Atom.wt`
as `Euf_Checker.checker` already does. A bridge relates an EO syntax node to
these checked table entries; it must not introduce a new `SmtModel`, a new
SMT-LIB evaluator, or an unconstrained Boolean valuation for theory atoms.
Reject tables with cycles/bad indices or inconsistent declarations at that
boundary. In an incremental arena, also prove that extending tables preserves
all previously represented terms and checked facts, or freeze tables first.

Reuse `EUF.check_trans`, `check_congr`, `check_congr_pred` and
`valid_check_trans`, `valid_check_congr`, `valid_check_congr_pred` for their
actual supported term shapes. They produce valid implication clauses, not
the unit conclusion of the CPC step. Resolve those clauses with the **exact**
checked premise facts, or prove the corresponding consequence bridge.
For Boolean congruence/equivalences, use existing CNF/resolution checkers and
their correctness theorems. Do not reinterpret Boolean formulas as arbitrary
uninterpreted atoms to bypass the missing propositional bridge.

For LIA, a certificate producer may propose `list ZMicromega.ZArithProof`
for the exact clause formed from negated premise literals and the generated
conclusion. `LIA.check_micromega` calls the existing `ZTautoChecker`, and
`valid_check_micromega` establishes the returned clause's validity. Check
that the returned clause is the requested one (modulo a proved clause
normalization), since failure returns `C._true`. Apply the same discipline
to EUF checkers. A semantic gate returning some valid clause is insufficient.
Then derive the recorded result using only the referenced premise clauses.
This can check an individual CPC inference; it cannot replace the CPC trace
with a new solver refutation of all input assertions.

Scope requires additional work. Store a locally derived `F` as a guarded
clause `not A1 or ... or not An or F`, where `A1..An` are the active local
assumptions. A pushed assumption has the tautological guarded fact for itself,
not an unconditional unit assertion in `S.t`. Resolve/transform guards using
verified clause operations, and on `step-pop` derive the generated implication
while discharging exactly the matching assumption. Metadata links the EO
fact, its clause view and its active scope; closed scopes remove their premise
bindings. Existing global roots remain unit clauses. Until the guard and
discharge proofs exist, reject `assume-push`, `step-pop`, and scoped proofs
as unsupported. Simply allowing these commands would make an otherwise
plausible `S.valid` invariant false.

Bind initial assumptions to the original tactic's reified roots and declaration
environment. Compare translated literals with those roots, or accept only a
checked transformation from roots. Proof-local declarations cannot redefine
an input symbol's meaning. An `include`/`reference` directive cannot change
the compiled calculus or provide an unchecked assertion. The final result
must be a closed false clause derived from these bound roots, not merely an
`unsat` marker or a Boolean `false` printed by the solver.

## Suggested executable contract

The names here are proposals for the compiler and core owners, not existing
APIs or additional assumptions. Keep generated code under the compiler owner's
directory and make the handwritten core depend on a small generated interface.

```text
SignatureBundle = {
  schema_version; signature_id; include_manifest;
  symbols_with_types_and_attributes; programs; rule_schemas;
  source_locations; operational_profile; unsupported_inventory
}

Step = {
  fresh_occurrence_id; rule_id; ordered_argument_term_ids;
  ordered_premise_occurrence_ids; optional_explicit_conclusion;
  scope_action; semantic_certificate
}

eval_rule(bundle, arena, fuel, rule_id, arguments, premise_EO_terms)
  -> Result(derived_EO_term, diagnostic)

translate_fact(checked_tables, arena, derived_EO_term)
  -> Result(literal_or_justified_clause_view, diagnostic)

check_semantic_step(checked_tables, state : S.t, scope_metadata,
                    exact_premise_bindings, derived_fact, certificate)
  -> Result(updated_state_and_fact_binding, diagnostic)
```

`rule_schemas` contain executable argument/premise patterns, guards and
conclusion programs derived from `declare-rule`, not just rule names. Programs
use a finite expression/pattern IR: constructors/application, local variables,
ordered matching, equality tests, guards, conditionals, primitive calls and
program calls. Fuel makes evaluation total without adding termination
assumptions; exhaustion is rejection. Structural or well-founded compiled
functions can later replace it after equivalence proofs.

The core's command sequence should perform the following checks atomically:

1. Resolve names to live earlier occurrence IDs in the current scope; bounds
   checks are explicit. Read premises from the state/metadata, not from formulas
   supplied independently in a certificate. Check metadata's EO/clause relation.
2. Check generated arity/pattern constraints and execute the generated program,
   including every side condition. Unknown rule/program/primitive or failed
   guard rejects the command and the entire proof.
3. Compare an explicit CPC conclusion with the derived term when one is present.
   An omitted conclusion is computed, not filled by an unverified parser guess.
4. Translate premises and result using the shared checked tables. Validate the
   attached semantic certificate for this exact inference. Internal certificate
   substeps may be multiple existing checker operations; inspect them all and
   require their final fact to be the requested guarded result.
5. Update `S.t` using proved state operations (`S.set_clause` and verified
   resolution/weakening); add a binding only after both operational and semantic
   checks succeed. Preserve an error state once any command fails.

Required proofs are preservation of table/metadata well-formedness and
`S.valid`, bridge consistency for each successful translation, correctness
of scope discharge, checked root initialization, and closed-refutation
soundness. Use the existing generic trace theorem (`_checker__correct`) where
its contract fits. A `Result` adapter may need a small failure/preservation
wrapper. Semantic support can be a proved per-rule consequence lemma or a
verified small-checker certificate, but neither path may bypass `eval_rule`.
These are future proof obligations, not lemmas introduced by this report.

Keep operational support and semantic support separately visible in a generated
coverage manifest. All rules seen in a proof must have both. Generate source
and dependency hashes for reproducibility, but do not treat hash agreement as
a semantic proof. Any serialized bundle read at runtime needs structural and
profile validation; a digest alone cannot make an arbitrary bundle trusted.

## Rocq optimization priorities

These preserve signature-generated rules; they do not substitute a manually
hard-coded CPC checker. Each optimized primitive or evaluator needs a proved
refinement to its simple reference implementation before replacing it.

* **Share syntax first.** Use stable IDs and the existing atom/form tables for
  object terms; an EO arena can retain meta-terms. Check acyclicity and the
  ID-to-node relation. Hashes choose buckets, while exact equality resolves
  collisions. Use iterative/fold-based trace traversal to avoid stack growth.
* **Memoize pure calls.** Cache by signature/program, full argument IDs and any
  type/declaration environment affecting computation. For type lookup or scoped
  symbols, use a frozen environment or include its identity. A cached successful
  result must satisfy the reference evaluation relation. Fuel exhaustion is not
  a stable semantic failure and must not become a reusable `Stuck` result.
  Arbitrary external cache entries cannot be accepted without validation.
* **Specialize primitives generically.** Implement verified operator-list
  length/nth/reverse/erase and multiset inclusion over shared IDs, preserving
  operator identity, nil checks and multiplicities. Reuse `PArray`/`Uint63`
  facilities under existing assumptions. A set-inclusion algorithm is not a
  refinement of multiset inclusion when duplicates occur.
* **Compile patterns once.** Turn ordered cases into decision trees, retain
  repeated-variable tests and fallback order, and share helper calls and local
  bindings. Prove correspondence with the simple IR interpreter; generation
  should be deterministic and reproducible from the signature manifest.
* **Separate ordering from equality.** Polynomial canonicalization depends on
  `$compare_var` / `eo::cmp`. A fresh-ID order or a hash order is not automatically
  the same operation. Either reproduce the pinned comparison contract or prove
  the ordering-parametric normalization/semantic refinement and document any
  change to CPC operational compatibility. Hash collisions cannot establish
  syntactic equality or erase a polynomial term.
* **Measure the checked path.** Eventually report parse/generation, generated
  evaluation, bridge/certificate checking and kernel-checking costs separately
  from solver time, along with term sharing/cache-hit statistics. Extraction or
  native execution results alone are not a proof of the tactic's conclusion.

Ethos's pinned `src/type_checker.cpp:586,713-740,854` supplies concrete evidence
of an evaluation trie and cached program-call results within an evaluation
call; that alone is not evidence of a cache shared across all proof steps. Its
`src/state.cpp:136-140` binds list primitives, and `type_checker.cpp` implements
their evaluation. This supports using memoization and generic primitive
specialization as early experiments. No speedup was measured in this job.

## Fail-closed milestones and integration handoff

Start with quantifier-free, first-order UF over declared sorts and Booleans,
plus integer literals/linear operations where requested. Reject unsupported
term-valued conditionals, object-level Real/coercions, higher-order values,
quantifiers, arrays, bitvectors, strings, sets, datatypes and unbridged skolems.
Operational use of type terms or internal rational coefficient structures is
distinct from admitting those theories in object-level assertions.

The first useful UF acceptance target is **all 15 steps** of the observed
`uf4` proof, including Boolean congruence and `eq-refl`. The first useful LIA
acceptance target includes the entire observed `lia1` proof surface, including
scopes, variadic congruence, list resolution and arithmetic rewrite guards.
A scope-free or normalization-only subset can be useful progress but must
report that it cannot yet accept this fixture. Unsupported proof commands
must fail even if their results appear unused. Numeric overflow, malformed
indices, missing premises, wrong explicit conclusions, changed roots,
unclosed scopes, `trust`, and exhausted evaluation budgets all reject.

Owners should agree on the IR/schema, clause-view invariant, premise metadata,
scope representation and error behavior before changing shared dune/tactic
files. Coordinator integration will need dependencies on the existing fol,
EUF, CNF, LIA and generic checker theories, generated-file dependencies on the
**whole include closure**, and a build rule comparing regeneration output.
The tactic must pass original roots/declarations and construct a Rocq proof
from the checked result. No dune stanza is proposed here because module
locations/ownership are not yet settled. No shared integration file was edited.

Meaningful future negative checks include a mutated argument/explicit
conclusion, missing or out-of-scope premise, changed root, incorrect list
multiplicity, mismatched transitivity endpoints, illegal arithmetic sign,
unknown primitive and an unsupported step before a valid final contradiction.
Each must reject, not merely fail to contribute a clause. Run `Print Assumptions`
on every new soundness lemma and the integrated final theorem; distinguish
existing primitive assumptions permitted by repository conventions from any
new assumption. No new lemma was added here, so no such audit is claimed.

## Reproducible command evidence

Commands were run from this worktree unless stated otherwise. The following
commands and results are selected reproducible evidence for this survey, not
build or acceptance-test claims. No dependency installation was necessary.

```sh
TC=/home/charles/code/friends/.toolchains
CVC="$TC/cvc5-1.4.2/cvc5-Linux-x86_64-static/bin/cvc5"
CPC="$TC/cvc5-1.4.2/cvc5-cvc5-1.4.2/proofs/eo/cpc"
EVID=/tmp/smtrocq-logos-design-evidence
git branch --show-current
git rev-parse HEAD
git -C /tmp/smtrocq-logos rev-parse HEAD
git -C /tmp/smtrocq-ethos rev-parse HEAD
git -C /tmp/smtrocq-logos status --porcelain
git -C /tmp/smtrocq-ethos status --porcelain
```

All exited 0. Branch and starting SHAs are recorded in the pin table; the two
status commands produced no output. `HEAD` above was queried before this
report's local commit.

The first shell comments fetch, without network escalation, exited **6** with
`Could not resolve host: api.github.com`. The same public read succeeded with
network escalation (exit 0). The later snapshot commands also all exited 0:

```sh
mkdir -p "$EVID"
curl -fLsS --max-time 30 \
  'https://api.github.com/repos/cvc5/logos/issues/485/comments?per_page=100' \
  -o "$EVID/issue-485-comments.json"
curl -fLsS --max-time 30 https://api.github.com/repos/cvc5/logos/issues/485 \
  -o "$EVID/issue-485.json"
curl -fLsS --max-time 30 \
  https://api.github.com/repos/cvc5/cvc5/git/ref/tags/cvc5-1.4.2 \
  -o "$EVID/cvc5-tag.json"
PYTHONDONTWRITEBYTECODE=1 python3 /tmp/smtrocq-ethos/tools/eoc/driver.py desugar --help
"$CVC" --version
"$CVC" --dump-proofs --proof-format=cpc unit-tests/files/lia1.smt2 > "$EVID/lia1.cpc"
"$CVC" --dump-proofs --proof-format=cpc unit-tests/files/uf4.smt2 > "$EVID/uf4.cpc"
wc -l "$EVID/lia1.cpc" "$EVID/uf4.cpc"
sha256sum "$EVID/lia1.cpc" "$EVID/uf4.cpc" /tmp/smtrocq-uf4.cpc
rg -o --no-filename ':rule [^ )]+' "$EVID/lia1.cpc" | sort | uniq -c
```

The help lists `desugar` with `--natives {embed,eo}`, `--semantics`, build/output
directories and the other compiler options. Solver version is in the pin table.
The dumps contain 188 and 30 lines respectively, each starting with `unsat`.
SHA-256 results:

| Artifact | SHA-256 |
| --- | --- |
| `lia1.cpc` | `e9288f5a03f1b53d21869a3a7d0cf75f251a9a8c59500c4748525e49bc0a8a35` |
| `uf4.cpc` and `/tmp/smtrocq-uf4.cpc` | `d1c63e1376b08984c71f31ab3ce59b44c5c5bd294689cf0367468ddd229b976c` |
| `issue-485.json` | `732a8682822aa502cf9ca4ab06339ae8fdfc4a4c7912d12136fbb34b6be944a1` |
| `issue-485-comments.json` | `65a31ef41cad5a96935b4b3820a022c1f2d20ddd236bf1fda0007dc2b6939d70` |
| `cpc-includes.sha256` | `4045d8eddb5a48c7db20ab355b10cccdddadfd7a400af2a05114fcb90ac0b08a` |

The `lia1` rule counts were:

```text
2 and_elim             2 and_intro            6 arith-elim-lt
5 arith-leq-norm       2 arith_mult_neg       4 arith_poly_norm
2 arith_sum_ub         3 bool-double-not-elim 3 chain_m_resolution
16 cong               9 eq_resolve          15 evaluate
2 int_tight_ub         2 modus_ponens         9 nary_cong
2 not_and             1 not_implies_elim1    1 not_implies_elim2
2 not_not_elim        2 not_or_elim          2 process_scope
10 refl               2 reordering           6 scope
4 symm                15 trans               2 true_elim
```

The include inventory was computed with the following Python logic (exit 0).
It is an inventory over these pinned files, not a general Eunoia parser or a
checker; its include matcher deliberately targets the files' observed syntax.

```sh
python3 - <<'PY'
import hashlib, pathlib, re
base = pathlib.Path('/home/charles/code/friends/.toolchains/cvc5-1.4.2/cvc5-cvc5-1.4.2/proofs/eo/cpc')
seen = set()
def visit(p):
    p = p.resolve()
    if p in seen: return
    seen.add(p)
    for rel in re.findall(r'^\(include "([^"]+)"\)', p.read_text(), re.M):
        visit(p.parent / rel)
visit(base / 'Cpc.eo')
rows, rules = [], []
for p in sorted(seen):
    data = p.read_bytes()
    rows.append((str(p.relative_to(base)), hashlib.sha256(data).hexdigest()))
    rules.extend(re.findall(r'^\(declare-rule\s+(\S+)', data.decode(), re.M))
manifest = ''.join(f'{digest}  {name}\n' for name, digest in rows)
pathlib.Path('/tmp/smtrocq-logos-design-evidence/cpc-includes.sha256').write_text(manifest)
print(len(seen), len(rules), len(set(rules)))
print(hashlib.sha256(manifest.encode()).hexdigest())
PY
```

Results: `35 609 609` and the include-manifest hash above. Public API snapshots,
dumps and the manifest remain in `$EVID`; they are disposable local evidence,
not repository fixtures or accepted certificates. No compiler build,
desugaring run, Rocq build, new soundness proof, tactic test or performance
benchmark was performed for this documentation-only change. The coordinator's
earlier baseline build/test results remain separate evidence.

Still incomplete: the generated executable subset, primitive fidelity checks,
semantic translation and certificate bridges, scope proof, root binding,
negative acceptance tests, build integration and checked-path benchmarks.

Documentation validation: `git diff --cached --check` exited 0. An inline
Python check exited 0 after checking all eight relative file links, balanced
code fences, and the fixture step/distinct-rule counts `(15, 6)` and
`(131, 27)`. `git diff --cached --numstat` showed only this new Markdown file;
there are no proof files requiring `Print Assumptions`. The reference checkouts
remained clean. The final local commit SHA is supplied in the handoff rather
than embedded in its own content.
