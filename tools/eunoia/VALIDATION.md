# Signature compiler child-job validation (2026-11-03)

Worktree: `/home/charles/.t3/worktrees/SMTRocq/t3-08d3adb3`.
Branch: `t3/eunoia-signature-compiler`.
Implementation commit: `f6b3b143ce56d154f420ef2cd8d504a7379f5a61`.
The subsequent test/documentation commit is reported in the child-job handoff.

## Passed checks

From the worktree root:

```sh
bash tools/eunoia/check-generated.sh
```

Exit **0**: 20 Python tests passed; pinned-source regeneration was byte-identical;
`EoSyntax.v`, `EoRuntime.v`, `CpcGenerated.v`, `TestGenerated.v`,
`MutatedGenerated.v`, and `RuntimeTests.v` compiled with Rocq 9.3.0; all 29
computation examples were kernel checked. The last example group includes
changed-helper-source changing actual generated computation, requirements
rejecting altered arguments, a failed first case not falling through, and
missing helper output types rejecting the rule.

The script's exact Rocq commands, in a temporary directory, are:

```sh
/home/charles/code/friends/.toolchains/smtrocq-env rocq compile -q -Q . SMTCoq.checker.eunoia EoSyntax.v
/home/charles/code/friends/.toolchains/smtrocq-env rocq compile -q -Q . SMTCoq.checker.eunoia EoRuntime.v
/home/charles/code/friends/.toolchains/smtrocq-env rocq compile -q -Q . SMTCoq.checker.eunoia CpcGenerated.v
/home/charles/code/friends/.toolchains/smtrocq-env rocq compile -q -Q . SMTCoq.checker.eunoia TestGenerated.v
/home/charles/code/friends/.toolchains/smtrocq-env rocq compile -q -Q . SMTCoq.checker.eunoia MutatedGenerated.v
/home/charles/code/friends/.toolchains/smtrocq-env rocq compile -q -Q . SMTCoq.checker.eunoia RuntimeTests.v
/home/charles/code/friends/.toolchains/smtrocq-env rocq check -silent -Q . SMTCoq.checker.eunoia SMTCoq.checker.eunoia.RuntimeTests
```

All exit **0**. Rocq prints an informational `register-all` warning for the
list-nested expression datatype. No soundness lemmas are added. The commands
`Print Assumptions helper_symmetry.` and `Print Assumptions
side_condition_reject.` in `RuntimeTests.v` both print **Closed under the
global context**.

Full original signature validation (not the reduced snapshot):

```sh
python3 tools/eunoia/compile.py /home/charles/code/friends/.toolchains/cvc5-1.4.2/cvc5-cvc5-1.4.2/proofs/eo/cpc/Cpc.eo --rules refl symm true_intro true_elim false_intro false_elim eq_resolve modus_ponens not_not_elim contra eq-refl eq-symm ite_eq --output /tmp/CpcActual.v --manifest /tmp/CpcActual.json
cmp theories/checker/eunoia/CpcGenerated.v /tmp/CpcActual.v
cmp tools/eunoia/cpc-manifest.json /tmp/CpcActual.json
sha256sum theories/checker/eunoia/CpcGenerated.v
```

Each exits **0**. The reader traversed 35 actual files; it compiled 13 rules
and one helper, explicitly excluding 596 rules. Generated SHA-256:
`ea2be8c3b1a5bdff01820456c598e6b7be17adddb538d5612c63cee65e02468e`.
The manifest records all 35 source hashes and the full excluded-rule list.

## Expected failures

```sh
python3 tools/eunoia/compile.py /home/charles/code/friends/.toolchains/cvc5-1.4.2/cvc5-cvc5-1.4.2/proofs/eo/cpc/Cpc.eo --rules trans --output /tmp/unsupported-cpc.v --manifest /tmp/unsupported-cpc.json
```

Exit **2**, diagnostic at `rules/Uf.eo:66`: only implicit Type binders supported;
`:list`/`:opaque` rejected. Neither output is emitted.

```sh
python3 tools/eunoia/compile.py /home/charles/code/friends/.toolchains/cvc5-1.4.2/cvc5-cvc5-1.4.2/proofs/eo/cpc/Cpc.eo --rules trust --output /tmp/trust-cpc.v --manifest /tmp/trust-cpc.json
```

Exit **2**, diagnostic at `Cpc.eo:635`: unsupported rule field `:premise-list`.
Neither output is emitted. The Python tests also reject `:sorry` itself.

Proof-hole audit:

```sh
rg -n '\b(Admitted|admit|Axiom|Parameter|Abort)\b' theories/checker/eunoia tools/eunoia --glob '*.v' --glob '*.py'
```

Exit **1**, no matches. `git diff --cached --check` exits **0**.

## Remaining work / limits

* No end-to-end CPC proof processing, tactic integration, or semantic soundness
  theorem is claimed. The complete UF sample is unsupported.
* The coordinator must wire the shared-Atom/Form term/clause adapter to the
  core's exact-premise/exact-conclusion API and its separate checked witness
  gate. See `INTERFACE.md`. No new SMT semantics were defined here.
* The core owner must include these modules in its local dune theory; shared
  dune/tactic files were not changed. This job used isolated Rocq compilation,
  not a new full-repository `dune runtest` run.
* Define-helper desugaring, variadic/list constructs, arithmetic/list native
  computations, and additional CPC rules remain unsupported. Unsupported
  selected dependencies diagnose and fail rather than dropping conditions.
* Semantic bridge proofs remain required. The untrusted syntax computation
  and caller-supplied type query cannot independently justify State updates.

No solver execution, dependency installation, push, PR, or external comment was
performed. The first local Git staging attempt exited 128 because the linked
Git metadata is outside the writable sandbox; the authorized local staging and
commit succeeded through escalation.
