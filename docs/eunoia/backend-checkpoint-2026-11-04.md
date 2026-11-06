# Backend development checkpoint (2026-11-04)

The backend now selects 84 pinned CPC declarations, including all 50 declarations
in `rules/Booleans.eo`, and 53 helper programs. The other 525 declarations fail
closed. Signature source bytes are unchanged. This is broader checked UF/LIA
coverage, not completion of either SMT-LIB logic or a competitive tactic.

## Implemented changes

- Raw Boolean purification and scoped assumptions retain their source syntax for
  generated rule computation and bind to the actual SMTCoq clauses. Seven new
  public regressions cover positive/negative predicates, disjunction, Boolean
  constants and reuse of a tactic on different tables.
- Bounded invocation-local syntax, derivation and successful-witness producer
  caches avoid repeated native work. They never authorize proof acceptance.
- `EunoiaMemo` proves checked sharing of exact local certificates. Every cache
  entry, including unused entries, is validated; every source occurrence still
  runs generated computation, syntax binding and scope/state checks. Adaptive
  selection retains the reference representation unless at least four entries
  are reused and at least 25% of steps reuse a certificate. Both emitters have
  fresh positive/corruption replays and independent kernel checks.
- The pinned Linux x86-64 cvc5 installer verifies archives, executable and the
  matching signature tree. Setup and tooling no longer require an author's
  private toolchain path. CI provisions Trakt and the pinned solver explicitly.

## Verification

The full root `dune runtest` passed after the main implementation. Final backend
CI commands passed after adaptive emission: live suites, Python tests, generated
fixture/mutation checks, fresh reference/shared replay and independent checking.
The final audit covered **82 named correctness/public theorem targets**, followed
by recursive independent kernel checking. No admitted proof or new axiom was
introduced. SMTCoq's inherited 52-name primitive-integer/proof-irrelevance
assumption baseline remains; this is not an axiom-free implementation.

Python suites comprise 48 generator tests, 13 installer/capture tests and 15
benchmark tests. The shared checker additionally has 13 proved acceptance and
corruption controls. Nix formatting passed; the legacy external Nix matrix
cannot build in this fork because its cache endpoint is unconfigured (curl URL
`//<hash>.narinfo`, exit 3). This is distinct from Nix package validation.

## Matched checked-tactic measurement

Frozen checker revision: `d3d76438b539fbda6670836233885e24cc102498`.
Rocq 9.2, OCaml 4.14.2, Dune 3.21.1, pinned cvc5 1.4.2. One repeat of the
unchanged 18-positive/two-negative workload, sequential fresh compiler processes,
30-second whole-compiler limit. No checker source or compiled artifact changed
between the before/after fingerprints (`integrity_passed = true`). A later
commit changed CI provisioning only. This shared-machine sample is not a
statistical performance study or an ablation against the old Rocq 9.3 report.

```sh
EUNOIA_CACHE_PROFILE=1 python3 -B benchmarks/eunoia/run.py \
  --backends verit cvc5_eunoia --repeat 1 --timeout 30 --jobs 2 --skip-build \
  --output /tmp/eunoia-final-adaptive-matrix
python3 -B benchmarks/eunoia/report.py /tmp/eunoia-final-adaptive-matrix/results.json
```

| Backend | Checked positives / scheduled | Rejected controls / scheduled | Checked tactic total (s) | Checked Qed total (s) |
| --- | ---: | ---: | ---: | ---: |
| cvc5_eunoia | 13/18 | 2/2 | 126.529 | 0.575 |
| verit | 18/18 | 2/2 | 1.351 | 0.512 |

Timing totals include only checked positive proofs; their solved sets can differ.
Each latency comparison below uses the same case and repeat checked by both backends.

| Backend pair | Shared checked attempts | Tactic totals (s), left / right | Qed totals (s), left / right |
| --- | ---: | ---: | ---: |
| cvc5_eunoia / verit | 13 | 126.529 / 1.036 | 0.575 / 0.315 |

Timing excludes failed, unavailable and negative attempts. Whole compiler timeouts
and tactic errors remain unsolved in the coverage denominator. Tactic and Qed
times are separate; solver-only time is unavailable.

Five Eunoia attempts timed out: `uf_nested_congruence`, `uf_equality_chain`,
`lia_disjunctive_bounds`, `lia_inconsistent_bounds`, `lia_two_sided_bound`.
The runner exited 1, correctly retaining these unsolved positives. Both negative
controls failed before a completed proof. Results/logs, proof audits and replay
artifacts are preserved locally under `_build/eunoia-evidence/`.

A separate two-repeat matched reference/forced-sharing experiment on `9f31bb6`
had 10/10 checked positive attempts and 4/4 rejected negative attempts on each
side, but no repeated certificates. Forced sharing was roughly neutral on four
sampled cases and slower on the smallest one (1.826 vs 2.298 seconds median
tactic time). The adaptive default avoids imposing that representation on
nonrepeating proofs. No end-to-end sharing speedup is established.

## Remaining work

1. Reduce final generated-checker computation, especially repeated stateless
   type and helper side conditions. Producer search is not the dominant measured
   cost. Any new memoized or specialized evaluator needs a pointwise refinement
   proof and matched measurements before replacing the current implementation.
2. Add the checked positive-denominator integer embedding described in
   `integer-cast-signature-coverage.md`. Parity/coefficient captures compute
   through the signature today, but raw Real/cast intermediates still cannot
   bind to the live integer checker. Preserve raw rule inputs and source steps;
   use existing SMTCoq integer semantics and exact floor for ground `to_int`.
3. Expand live coverage and difficult UF/LIA workloads, then establish competitive
   results before adding more theories. No comparison with Lean-SMT,
   Sledgehammer or Logos has been measured in this environment.
