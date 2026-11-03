# UF signature computation validation

Run `EUNOIA_KEEP_TEST_DIR=1 tools/eunoia/check-generated.sh` from the repository.
The script prints the retained artifact directory and uses only Python plus
`/home/charles/code/friends/.toolchains/smtrocq-env rocq`.
It regenerates both `CpcGenerated.v` and its manifest from the complete pinned
cvc5 1.4.2 include closure and compares both byte-for-byte. It compiles isolated
copies under `-Q . SMTCoq.checker.eunoia` in dependency order:

```
EoSyntax EoRuntime CpcGenerated TestGenerated MutatedGenerated
MutatedCpcGenerated TraceReplay RuntimeTests FixtureTests TraceNegativeTests
```

Then it runs independent recursive kernel checking of `RuntimeTests`,
`FixtureTests`, and `TraceNegativeTests` with `rocq check -silent`, without
admission flags. `Print Assumptions` is embedded in the regression modules;
all printed computational facts are closed under the global context. This
work adds no semantic soundness lemma, assumption, or SMT interpretation.

`replay_fixtures.py` decodes the actual CPC commands and nullary term definitions
into Rocq data. It computes **no** rule conclusion in Python. `TraceReplay.v`
fetches exact ordered premise terms and calls generated `derive` on every step,
requiring all explicit conclusions to agree. Missing/forward/duplicate IDs,
unsupported commands and unknown rules reject; the test decoder does not handle
scopes. An input `unsat` marker alone is never evidence. The final result must
be the actual generated `false` term after the entire trace has run. This is
signature coverage, not acceptance by the semantic State checker.

| Actual fixture | Steps replayed |
| --- | ---: |
| uf1 | 25 |
| uf2 | 9 |
| uf3 | 14 |
| uf4 | 15 |
| uf5 | 22 |
| uf6 | 10 |
| uf7 | 3 |

These exercise `aci_norm`, `and_elim`, `chain_m_resolution`, `chain_resolution`,
`cnf_and_pos`, `cnf_or_pos`, `cong`, `contra`, `eq-refl`, `eq_resolve`, `evaluate`,
`nary_cong`, `refl`, `resolution`, `trans`. Twelve further selected small rules
retain regression coverage from the initial generator tests or are simple
source-generated extensions; the manifest lists all 27 selected rules.

Negative trace tests corrupt an index, congruence's repeated variable, premise
multiplicity and the explicit final conclusion. Unknown unused steps both
before and **after** the conflict reject. Mutating the actual source helper
`$mk_trans` guard changes computation and rejects the original `uf4` trace.
The previous source-mutation test also changes a novel helper body, with a
kernel-checked change of its result. Generic runtime tests cover ordered case
commitment, lazy/unused failures, parallel let scope, definition capture,
Boolean equality, invalid lists and out-of-bounds/negative indices, duplicate
preservation, multiset equality/inclusion/difference/intersection, and exhausted
fuel. No rule-name code replaces source generation.

The coordinator still owns integration with `EunoiaAdapter` and `EunoiaLocal`:
each exact generated result needs its verified semantic certificate and shared
Atom/Form entries. Neither this replay nor `Print Assumptions` of its computed
facts establishes soundness of CPC rules or of a full SMT-LIB refutation.
Unsupported rules, arithmetic/dependent nils, mixed Real/Int semantics,
production scoped reader/tactic wiring, and full backend coverage remain open.

The dependent scope extension adds generic source `:assumption` patterns,
`derive_assuming`, source-generated `scope` and ordinary `process_scope`.
Seventeen additional Rocq examples check exact pushed formula matching,
Boolean typing, repeated variables, guards, missing/extra premises, rejection
through the wrong entry point, and nested antecedent collection with exact flat
surface output. No scoped semantic checker or production scoped reader is
claimed; the coordinator supplies the proved conditional invariant/discharge.
