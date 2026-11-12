# Preparatory UF coverage for cvc5 1.4.2 CPC

This is an inventory and a verified bridge to existing SMTCoq checkers. It is
**not** an operational CPC backend or a claim that any complete CPC proof has
been replayed in Rocq. All steps, including the Boolean steps surrounding UF,
still need signature-generated checking and semantic certificates.

## Sources and reproduction

Work started from `2e1c1a7` on child branch `t3/uf-eunoia-coverage`, descended from
`smtrocq/cvc5-eunoia`. The implementation contract is
[implementation-plan.md](implementation-plan.md). Repository conventions used:
existing `EUF.v`/`Terms.v`/`State.v`, their imports and CeCILL-C header, and the
existing EUF theory's dune dependencies. No applicable `AGENTS.md` was present.
No generator, core, shared dune, or tactic file is changed.

Local sources inspected:

* Solver: `/home/charles/code/friends/.toolchains/cvc5-1.4.2/cvc5-Linux-x86_64-static/bin/cvc5`
  (1.4.2, upstream commit `282d5e0`).
* Matching signature root:
  `/home/charles/code/friends/.toolchains/cvc5-1.4.2/cvc5-cvc5-1.4.2/proofs/eo/cpc/`.
  In particular: `Cpc.eo`, `rules/Uf.eo`, `rules/Booleans.eo`,
  `rules/Rewrites.eo`, `rules/Quantifiers.eo` (`skolem_intro`), and
  `theories/Builtin.eo`.
* Existing actual sample `/tmp/smtrocq-uf4.cpc`.
* Logos checkout identity verified as
  `89df5909b0e9aabb936b68ee95c75a18f609db7a` at `/tmp/smtrocq-logos`;
  no Logos proof or semantics is imported. Ethos was not used.

From the repository root, the exact successful inventory command was:

```sh
python3 docs/eunoia/uf-probe.py \
  --cvc5 /home/charles/code/friends/.toolchains/cvc5-1.4.2/cvc5-Linux-x86_64-static/bin/cvc5 \
  --out /tmp/smtrocq-uf-coverage
```

Exit code **0**. The script materializes the ten representative inputs, runs
all seven existing UF inputs plus those inputs with
`--dump-proofs --proof-format=cpc --check-proofs --check-proofs-complete`, and
records each exact command, exit code, source/proof SHA-256, and rule counts in
`/tmp/smtrocq-uf-coverage/inventory.json`. Each solver invocation exited **0**,
reported `unsat`, and had empty stderr. Proofs and input fixtures remain under
that `/tmp` directory. Solver-internal proof checks provide diagnostic evidence;
they are not the Rocq trust boundary. No result here is used to prove a theorem.

The probe only inventories rule tokens in solver output. It is not a CPC parser,
rule evaluator, or certificate checker.

## Actual rules in the seven existing inputs

Counts below are emitted CPC `step` counts, excluding declarations and `assume`.
These default proofs total **98 steps**, using **15 different rules**.

| Input | Steps | Actual rules, with multiplicity |
| --- | ---: | --- |
| `uf1.smt2` | 25 | `aci_norm` 1, `and_elim` 5, `chain_m_resolution` 1, `cong` 8, `eq-refl` 1, `eq_resolve` 1, `evaluate` 1, `nary_cong` 3, `refl` 1, `trans` 3 |
| `uf2.smt2` | 9 | `and_elim` 2, `chain_resolution` 1, `cnf_and_pos` 2, `cnf_or_pos` 1, `contra` 1, `resolution` 2 |
| `uf3.smt2` | 14 | `and_elim` 3, `cong` 4, `eq-refl` 1, `eq_resolve` 1, `evaluate` 1, `refl` 1, `trans` 3 |
| `uf4.smt2` | 15 | `and_elim` 3, `cong` 6, `eq-refl` 1, `eq_resolve` 2, `evaluate` 1, `trans` 2 |
| `uf5.smt2` | 22 | `and_elim` 6, `cong` 4, `eq-refl` 1, `eq_resolve` 2, `evaluate` 1, `refl` 2, `trans` 6 |
| `uf6.smt2` | 10 | `cong` 4, `eq-refl` 1, `eq_resolve` 1, `evaluate` 1, `refl` 1, `trans` 2 |
| `uf7.smt2` | 3 | `chain_m_resolution` 1, `cong` 1, `eq_resolve` 1 |

`uf2` needs only Boolean reasoning; its uninterpreted predicates do not cause
any equality/congruence proof steps. `uf6` exercises a binary function with an
unchanged first argument. `uf7` exercises a binary Boolean-valued predicate.
`uf1` needs n-ary Boolean congruence and ACI normalization in addition to UF.
`uf5`'s CPC proof rewrites equalities inside equalities before transitivity, so
an implementation that recognizes only flat term-equality chains misses steps.

## Representative integer and Boolean tactic goals

The fixture generator in [uf-probe.py](uf-probe.py) gives the exact SMT inputs.
They negate the indicated tactic conclusions and assert the hypotheses. The
integer congruence/symmetry/binary-function cases correspond to
`unit-tests/lfsc_tactics.v`, section `EUF` (both propositional equality and
`Z.eqb`/Boolean implication variants). They do not exercise the new tactic,
which does not yet exist. These inputs add **78 steps**; the combined rule
inventory contains **20 different rules**.

| Fixture | Goal shape | Steps | Rules |
| --- | --- | ---: | --- |
| `int-congr-reverse` | `y=x -> f x=f y` | 11 | `cong` 4, `eq-refl` 1, `eq_resolve` 1, `evaluate` 1, `refl` 1, `symm` 1, `trans` 2 |
| `int-symm` | `f x=f y -> f y=f x` | 2 | `contra` 1, `symm` 1 |
| `int-trans` | `x=y -> y=z -> x=z` | 10 | `cong` 3, `eq-refl` 1, `eq_resolve` 1, `evaluate` 1, `refl` 1, `trans` 3 |
| `int-congr2` | `x=y -> g z x=g z y` | 10 | `cong` 4, `eq-refl` 1, `eq_resolve` 1, `evaluate` 1, `refl` 1, `trans` 2 |
| `int-neg-symm` | `x<>y -> y<>x` | 2 | `contra` 1, `symm` 1 |
| `int-predicate` | `x=y -> P x -> P y` | 3 | `chain_m_resolution` 1, `cong` 1, `eq_resolve` 1 |
| `int-affine-uf` | `x+1=y+1 -> f y=f x` | 16 | `arith_poly_norm` 3, `arith_poly_norm_rel` 1, `cong` 5, `eq-refl` 1, `eq_resolve` 3, `evaluate` 1, `trans` 2 |
| `bool-domain-congr` | `x=y -> f x=f y`, `f:Bool->Int` | 10 | `cong` 4, `eq-refl` 1, `eq_resolve` 1, `evaluate` 1, `refl` 1, `trans` 2 |
| `bool-result-congr` | `x=y -> f x -> f y`, `f:Bool->Bool` | 12 | `chain_m_resolution` 1, `cong` 4, `eq-refl` 1, `eq_resolve` 2, `skolem_intro` 1, `trans` 2, `true_elim` 1 |
| `bool-neg-symm` | `x<>y -> y<>x`, `x,y:Bool` | 2 | `contra` 1, `symm` 1 |

In the two negated-symmetry fixtures the emitted `symm` operates on the positive
equality from the negated conclusion, then `contra` closes the contradiction.
They do not demonstrate an emitted negative-premise `symm` step. The signature's
`$mk_symm` does support disequality; the bridge below supports that case too.

The Bool-to-Bool proof introduces `(@purify y)` through `skolem_intro` and uses
`true_elim` before congruence. The frontend must provide checked handling of
this construct or reject that proof. A bare fresh unconstrained symbol does not
justify the purification equality. The affine input needs the LIA owner's
normalization bridge; integer carrier support alone does not cover it.

## Mapping onto existing semantics and checkers

| CPC obligation | Existing SMTCoq material | Required connection / current limit |
| --- | --- | --- |
| `refl`, term equality | `Atom.BO_eq`, `EUF.check_trans`, `EUF.valid_check_trans` | Empty equality list proves a well-typed reflexive equality. |
| Positive `symm`, `trans` | Same transitivity checker and theorem | One-element chain gives symmetry. Check the exact generated conclusion and premise clause. CPC `$mk_trans` requires ordered matching endpoints; the EUF checker is more permissive about orientation, so it cannot replace the generated CPC side conditions. |
| Negative `symm` | Positive symmetry certificate, `Lit.interp_neg` | Check the converse positive implication, then contrapose; see `neg_symm_step_sound`. |
| UF `cong` with non-Boolean result | `EUF.check_congr`, `EUF.valid_check_congr`, `EUF.build_congr_correct` | Same function/operator; one option per flattened argument. `None` requires identical argument IDs; `Some l` requires an equality of those exact arguments in either direction. |
| Predicate `cong` | `EUF.check_congr_pred`, `EUF.valid_check_congr_pred` | Checks the directional clause from `P a` to `P b` under argument equalities; use the reverse checker call as well if certifying their Boolean equality as an `Fiff`. |
| Boolean `cong`, `nary_cong`, including `not` and equality contexts | `Form.Fiff`, signed literals, `Form.wf_interp_form`, CNF's `valid_check_BuildDef`, `valid_check_BuildDef2`, `valid_check_BuildProj` | Compose existing Boolean certificates for the exact reified formulas. EUF's term-equality accessor does not accept `Fiff`; it cannot directly check an equality between arbitrary Boolean forms. No such adapter is added here. |
| `eq-refl` | Reflexive EUF certificate plus Boolean/CNF bridge | Signature conclusion is `(= (= t t) true)`, distinct from `refl`'s `(= t t)`; the outer equality needs its own certificate. |
| `eq_resolve`, `true_elim` | `Form.Fiff` interpretation and existing CNF/resolution checkers | Bind both sides of the Boolean equality and the exact source premise; e.g. CNF implications plus resolution. No raw rewrite of arbitrary IDs. |
| `and_elim`, `cnf_and_pos`, `cnf_or_pos` | CNF projection/definition checkers and their soundness lemmas | Bind the n-ary index, polarity, exact premises and exact result. |
| `resolution`, `chain_resolution`, `chain_m_resolution`, `contra` | `C.resolve_correct`, `S.valid_set_resolve`; Boolean complement via `Lit.interp_neg` | Verify generated pivots/side conditions as well as the exact clause result, rather than accepting a tautological fallback. |
| `evaluate`, `aci_norm` | Existing `Form` interpretation, CNF; `Syntactic.check_flatten_aux_correct` as a possible Boolean normalization ingredient | Generated evaluation and all normalization side conditions remain necessary. These existing lemmas are ingredients, not a proof of arbitrary CPC evaluation or ACI normalization. |
| `arith_poly_norm`, `arith_poly_norm_rel` | Existing `Atom` integer semantics and LIA checker | LIA integration needed; do not treat these as UF transitivity. |
| `skolem_intro` / `@purify` | Shared term interpretation and definitional binding | Checked definition/reification connection needed; unsupported forms must fail closed. |

CPC `cong` uses curried applications and reverses its premise list internally.
In `uf6` the proof changes only the final argument of `(f z x)`. Flattening to
`Atom.Aapp f [z;x]` therefore needs `[None; Some eq_xy]`, not a one-element
argument certificate. `None` also prevents an unchanged argument from becoming
an unbound or fabricated CPC premise. Higher-order function equalities and
partial applications as values are not covered by this first-order mapping.

`Typ.TZ`, `Typ.Tbool`, and `Typ.Tindex` already supply the carrier choices.
The new lemmas are polymorphic in the existing type/function tables and do not
introduce another equality or interpretation. Boolean variables used as UF
arguments may have atom representations, while compound Boolean formulas use
`Form`; their linkage must be proved by the frontend, including purification.

## Bridge module and minimal interface to generator/core

[../../theories/checker/eunoia/EunoiaUf.v](../../theories/checker/eunoia/EunoiaUf.v)
exports five lemmas:

* `trans_clause_sound`, `congr_clause_sound`, `pred_congr_clause_sound` transfer
  the corresponding existing EUF theorem to an **exactly equal** claimed clause.
* `unit_consequence` uses `C.Cinterp_neg` to derive a conclusion from a valid
  clause `conclusion :: map Lit.neg premises` and satisfied premise literals.
* `neg_symm_step_sound` derives `~forward -> ~backward` from the checked clause
  `forward \/ ~backward`. For `forward=(x=y)` and `backward=(y=x)` this is the
  negative symmetry rule. It does not pass negative literals to `get_eq`.

The interface requires existing `t_i`, `t_func`, `t_atom`, `t_form`, together
with `Atom.check_atom t_atom`, `Form.check_form t_form`, and
`Atom.wt t_i t_func t_atom`. These are discharged table checks, not new global
assumptions. The valuation is exactly
`Form.interp_state_var (Atom.interp_form_hatom ...)
(Atom.interp_form_hatom_bv ...) t_form`.

The generator/core must supply:

1. The signature-derived rule result and successful side conditions, including
   ordered premises, arity, types, argument order, and symbol identity. An EUF
   certificate alone does not prove that a CPC rule was applied as specified.
2. A faithful term-to-atom / formula-to-literal map with a checked interpretation
   connection, preserving equality endpoints, shared heads, sorts, and signs.
   Equality on Boolean forms must be linked to `Form.Fiff`, not mistaken for an
   atom equality accepted by `get_eq`.
3. Bound root assertions and scoped assumptions, explicit successful premise
   lookups, and exact correspondence to `S.get s cid`. Missing/out-of-range IDs
   and unsupported nodes must fail; an array default is not a supplied premise.
   For unit-premise inference, unitness and literal identity must be checked.
4. A reflected syntactic clause comparison that implies the equality used by
   these lemmas. **Do not** accept merely because an EUF checker returned a
   clause: malformed inputs return `C._true`. **Do not** pass disequalities as
   positive premises: the equality accessor strips signs. The target clause
   must be built from the exact signed CPC premises and conclusion.
5. Explicit treatment of clause order. A successful chain gives
   `res :: rev (map neg eqs)` for positive equality literals. A successful
   congruence gives the reversed supplied equality negations before the result;
   predicate congruence ends with `neg pa; pb`. The `None` entries add nothing.
   A core may instead compare `S.sort` on both clauses and use
   `S.sort_correct` with the same well-formed valuation. Neither clause order
   changes nor omitted premises should be silently assumed by the bridge.
6. State insertion using `S.valid_set_clause` / `S.valid_set_clause_keep`, with
   valuation well-formedness from `Form.check_form_correct`, and premise
   validity from `S.valid_get`. `S.valid_set_resolve` handles checked resolution
   insertion; terminal contradiction uses `C.is_false_correct`. Root binding,
   scope discharge, preservation, and full refutation soundness remain core work.

These requirements permit the UF work to be consumed before generated syntax
is fixed. There is no rule-name switch, CPC parser, or generated-rule substitute
in `EunoiaUf.v`.

## Negative and positive kernel-checked evidence

The module contains **21** computed regression theorems. Six demonstrate
reflexivity, symmetry, transitivity, reversed equality orientation, function
congruence with an unchanged argument, and predicate congruence. The others
check non-reflexive empty chains, disconnected chains, wrong endpoints,
non-equality atoms, Boolean forms incorrectly treated as atom equalities,
different function heads, too few argument certificates, changed arguments with
`None`, wrong supplied argument equalities, out-of-bounds equalities, and wrong
predicate argument equalities. They also demonstrate sign erasure and prove
that a negative-premise clause, a negative conclusion, and a malformed
congruence's fallback cannot match the requested signed clause.

The regression tables test checker syntax. They are not passed off as checked
well-typed tables and are not used as semantic hypotheses. Each regression is
proved with kernel-checked computation (`vm_compute`, then reflexivity or
discrimination). No solver answer proves one of them.

## Build and assumption audit

The exact baseline build command was:

```sh
/home/charles/code/friends/.toolchains/smtrocq-env dune build theories
```

Exit code **0**, existing deprecation warnings only. The new directory has no
dune stanza, so that command establishes the existing modules, not inclusion of
the new file in the normal build. A successful isolated compile, including all
21 regressions, used:

```sh
mkdir -p /tmp/smtrocq-uf-coverage/rocq
cp theories/checker/eunoia/EunoiaUf.v /tmp/smtrocq-uf-coverage/rocq/EunoiaUf.v
uf_rocq_args=(
  -Q _build/default/theories/utils SMTCoq.utils
  -Q _build/default/theories/structures SMTCoq.structures
  -Q _build/default/theories/checker/fol SMTCoq.checker.fol
  -Q _build/default/theories/checker/small-checkers/euf SMTCoq.checker.small_checker.euf
  -Q /tmp/smtrocq-uf-coverage/rocq SMTCoq.checker.eunoia
)
/home/charles/code/friends/.toolchains/smtrocq-env rocq c "${uf_rocq_args[@]}" \
  /tmp/smtrocq-uf-coverage/rocq/EunoiaUf.v
```

Exit code **0**, no output. Copying into the mapped temporary directory keeps
the correct logical library name and all compiled artifacts out of the source
tree. For each new soundness lemma and each existing comparison theorem, the
audit compiles a separate file containing `Print Assumptions <name>.` with the
same wrapper and flags. Exact reproducible audit commands:

```sh
for uf_lemma in unit_consequence trans_clause_sound congr_clause_sound \
  pred_congr_clause_sound neg_symm_step_sound EUF.valid_check_trans \
  EUF.valid_check_congr EUF.valid_check_congr_pred C.Cinterp_neg; do
  uf_audit="/tmp/smtrocq-uf-coverage/rocq/${uf_lemma//./_}Assumptions"
  cat > "${uf_audit}.v" <<EOF_AUDIT
From SMTCoq.checker.eunoia Require Import EunoiaUf.
From SMTCoq.checker.small_checker.euf Require Import EUF.
From SMTCoq.checker.fol Require Import State.
Print Assumptions ${uf_lemma}.
EOF_AUDIT
  /home/charles/code/friends/.toolchains/smtrocq-env rocq c "${uf_rocq_args[@]}" \
    "${uf_audit}.v" > "${uf_audit}.log" 2>&1 || exit "$?"
done
```

Every audit invocation exited **0**. Logs are under
`/tmp/smtrocq-uf-coverage/rocq/*Assumptions.log`. The new lemmas do **not** print
“Closed under the global context”: existing EUF soundness depends on the
standard `PrimInt63`/`Uint63Axioms` declarations and
`ProofIrrelevance.proof_irrelevance`. Comparing the printed assumption-name
sets shows no additions beyond the corresponding existing checker theorem
(`C.Cinterp_neg` for `unit_consequence`, `EUF.valid_check_trans` also for
`neg_symm_step_sound`). No new axiom, parameter, or proof hole is introduced.

Coordinator-owned dune integration, if a separate theory remains appropriate:

```lisp
(rocq.theory
 (generate_project_file)
 (package rocq-smtcoq)
 (name SMTCoq.checker.eunoia)
 (theories Stdlib SMTCoq.utils SMTCoq.structures SMTCoq.checker.fol
           SMTCoq.checker.small_checker.euf))
```

The coordinator must reconcile this with the eventual core/generated modules;
this suggested stanza was not installed. No shared tactic change is needed to
compile this preparatory module. `dune runtest` was not rerun here, and no claim
is made about the coordinator's earlier running test suite.

Remaining work: generated CPC application checking; exact root/premise/state
binding and clause comparison; Boolean form/atom and purification bridges;
certificates for every emitted Boolean/rewrite/normalization step; LIA
normalization integration; whole-proof replay including negative mutations;
and tactic/build integration. This inventory and isolated module do not settle
those integration obligations.
