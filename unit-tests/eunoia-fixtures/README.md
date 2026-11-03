# Unverified cvc5 1.4.2 CPC fixtures

These are **raw solver outputs, not verified proofs or accepted SMTCoq
certificates**. No Ethos, Logos, or Rocq checker was run on them. Successful
capture, an `unsat` line, cvc5's internal checks, and absence of `trust` establish
no independent soundness claim. Every inference and exact root assumption still
needs checking by the signature-generated SMTCoq backend.

The four retained dumps total 11,785 bytes and preserve the solver's original
stdout, including `unsat` and the enclosing proof block:

| Fixture | Existing input | Purpose | Printed steps |
| --- | --- | --- | ---: |
| `default/uf4.cpc` | `unit-tests/files/uf4.smt2` | Equality substitution, congruence, contradiction | 15 |
| `reduced/uf6.cpc` | `unit-tests/files/uf6.smt2` | Binary-function congruence, scoped implication and resolution with preprocessing reduced | 6 |
| `default/lia1.cpc` | `unit-tests/files/lia1.smt2` | Branching linear bounds, arithmetic sums, integer tightening, nested scopes | 131 |
| `default/lia3.cpc` | `unit-tests/files/lia3.smt2` | Integer strict-inequality normalization and polynomial normalization | 28 |

The unchanged inputs are reused from `unit-tests/files/`; they are not rewritten
or copied. Input SHA256, raw output SHA256/size, exact solver argv, source
revision, stderr SHA256, and the matched toolchain/archive/signature pins are in
[`regression-inventory.json`](regression-inventory.json). [`fixtures.json`](fixtures.json)
selects the four retained outputs and pins that full capture report. The other
24 dumps and all stderr files remain transient; their report paths refer to the
capture directory when regenerated. All recorded solver exits were 0 and all
stderr streams were empty.

The capture used script commit `9f3abbf215ef2a75e1ba572f2648427465a63aeb` on
2026-11-03. Its inputs have the same contents as implementation-plan commit
`2e1c1a7`. Exact command from the repository root (exit 0, 28 dumps):

```sh
/home/charles/code/friends/.toolchains/smtrocq-env \
  python3 -B scripts/eunoia/dump_cpc.py \
  --toolchain-root /home/charles/code/friends/.toolchains \
  --output /tmp/smtrocq-eunoia-9f3abbf
```

Choose a new output directory for replay; the script never overwrites one.
Replays at another revision record that revision in their report. No timestamps
or timings affect the dump bytes; this inventory is not a performance benchmark.

The verified private executable is
`/home/charles/code/friends/.toolchains/cvc5-1.4.2/cvc5-Linux-x86_64-static/bin/cvc5`,
version `1.4.2`, revision `282d5e0`, SHA256
`6aecddf466552b83bb5883756c7955e0c9d5ddcc6d7f45b48c2f6e06a741b102`.
Its matching signature entrypoint is
`/home/charles/code/friends/.toolchains/cvc5-1.4.2/cvc5-cvc5-1.4.2/proofs/eo/cpc/Cpc.eo`,
SHA256 `d13767eb873649c9f40482c99242c42081cf25308962f11c1981ce8e878770ad`.
All 51 CPC tree files matched the source archive; the tree digest is
`851569e9ec889d1747054ea014279c43bc02c1585f0468ab0773e65663fd1f8c`.
Archive URLs/hashes are pinned in
[`scripts/eunoia/cvc5-1.4.2.json`](../../scripts/eunoia/cvc5-1.4.2.json).

All 14 existing regressions (`uf1`–`uf7`, `lia1`–`lia7`) were captured under both
profiles. Counts below include every printed `step` and `step-pop`; repeated
step identifiers printed again in separate scopes are counted as occurrences.

| Profile | UF steps / distinct rules | LIA steps / distinct rules | Total steps / distinct rules |
| --- | ---: | ---: | ---: |
| `default` | 98 / 15 | 379 / 33 | 477 / 37 |
| `reduced` | 93 / 14 | 392 / 35 | 485 / 39 |

Default UF rules, exactly as printed:

```text
aci_norm and_elim chain_m_resolution chain_resolution cnf_and_pos cnf_or_pos
cong contra eq-refl eq_resolve evaluate nary_cong refl resolution trans
```

Default LIA rules, exactly as printed:

```text
and_elim and_intro arith-elim-gt arith-elim-leq arith-elim-lt arith-leq-norm
arith_mult_neg arith_poly_norm arith_poly_norm_rel arith_sum_ub
bool-double-not-elim chain_m_resolution cnf_and_pos cong contra eq-refl
eq_resolve evaluate int_tight_ub modus_ponens nary_cong not_and
not_implies_elim1 not_implies_elim2 not_not_elim not_or_elim process_scope
refl reordering scope symm trans true_elim
```

Across the full corpus, `reduced` adds `arith-eq-elim-int`, `cnf_and_neg`,
`implies_elim`, and `true_intro`, and removes `chain_resolution` and `cnf_or_pos`.
The JSON gives counts per input and profile, plus the signature file declaring
each observed rule. No observed rule was absent from the actual include closure
or marked `:sorry`. The two profiles together exercise 41 distinct rule names.
This is a small regression inventory, not coverage of all QF_UF/QF_LIA proofs.

Options that affect the initial coverage burden:

* `--simplification=none` disables nonclausal simplification. Together with
  `--no-static-learning --no-ite-simp --no-unconstrained-simp --no-repeat-simp`
  it defines the reproducible `reduced` profile. It can make individual EUF
  proofs much smaller (`uf4`: 15 to 8 printed steps; `uf6`: 10 to 6). It shifts
  work to Boolean resolution and scopes, and **increases** the total rule set
  and LIA steps here. Do not assume disabled preprocessing reduces coverage.
* `--proof-granularity=dsl-rewrite` requests detailed rewrites instead of opaque
  macro explanations. It remains enabled in both profiles: choosing coarse
  proofs to hide unsupported steps is not an acceptable shortcut.
* `--no-proof-allow-trust` and `--check-proofs-complete` request failure on
  incomplete solver explanations. The inventory independently rejects any rule
  marked `:sorry` in the loaded signature. Neither mechanism replaces semantic
  verification of supported rules and exact premises/conclusions.

The next integration work is the signature compiler, checked root/premise/scope
binding, and reuse of the existing verified EUF/LIA checkers. These tools add no
Rocq lemma or soundness assumption; `Print Assumptions` is therefore not
applicable to this change. No shared dune/tactic edits are required here.
