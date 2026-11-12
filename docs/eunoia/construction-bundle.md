# Combined proof-construction result

The default avoids duplicate VM goal reduction inside checked private proof
helpers and shares the exact complete trace through a checked transparent data
definition. Source evaluation, semantic gates, ordered roots/premises, scope
checks and unused source steps remain checked. Helper types and their universe
constraints are checked before use. Neither optimization caches a verdict or
introduces an axiom or admitted proof.

Set both `EUNOIA_SINGLE_KERNEL_ACCEPTANCE=0` and `EUNOIA_TRACE_CONSTANTS=0` to
restore the preceding proof-construction paths. Program indexing, staged/direct
helpers and helper mining remain disabled by default because their full-tactic
comparisons did not establish improvements.

## Balanced stability comparison

Frozen commit `b6a1c70` ran reference/optimized/optimized/reference twice, with
fresh compiler processes, the same checker sources/artifacts, identical goals,
printed conclusions, adaptive certificate sharing and unchanged 30-second
compiler timeouts. Only the two proof-construction flags changed. The reference
uses the same current checker with both optimizations disabled.

The initial sequence showed control outliers (one veriT case took 0.946 s
versus 0.124 s in another round), so the entire balanced sequence was repeated.
All eight rounds and every sample are retained; none were removed. Each
path/backend proved all **72 positive attempts** and rejected all **eight false
controls**. Checker fingerprints were identical across all eight rounds and
workload hashes matched. A documentation-only initial report was generated
during the repeat; executable sources and built artifacts remained unchanged.

The sum of per-case medians (four samples for each of 18 positive cases) is:

| Path | Tactic | `Qed` | Median tactic + `Qed` |
| --- | ---: | ---: | ---: |
| CVC5/Eunoia reference | 27.7335 s | 0.9215 s | 28.6855 s |
| CVC5/Eunoia optimized | 15.2335 s | 0.5355 s | 15.8030 s |
| veriT reference control | 1.5495 s | 0.6355 s | 2.1860 s |
| veriT optimized control | 1.5305 s | 0.6110 s | 2.1465 s |

This is **45.1% less CVC5/Eunoia tactic time**, or **44.9% less including
`Qed`**. The median-based veriT tactic control changed by 1.2%. Combined medians
are computed from paired tactic-plus-`Qed` samples, so they need not equal the
sum of the two separately computed medians. The optimized backend remains
about **10 times slower than veriT** on tactic time in this suite. These results
do not establish competitiveness with other provers or complete theory support.

Raw totals across all samples, including outliers, are 117.008/62.820 s of
CVC5/Eunoia tactic time and 3.905/2.256 s of `Qed`; veriT controls are
7.445/6.299 s and 2.768/2.748 s respectively. The raw control variation is why
both raw rows and per-case medians are reported.

[All eight rounds, counts, hashes and summary statistics](construction-bundle-stability-2026-11-05.json)
retain the evidence. The [initial sequence](construction-bundle-comparison-2026-11-05.json)
is also retained separately. Individual optimization reports are
[private proof acceptance](kernel-acceptance.md) and
[transparent trace sharing](trace-data-sharing.md).

Validation includes the full default build/regression, 308 named assumption
audits with independent kernel checking, and 19 fresh trace-sharing evaluator
and public fixture groups with independent kernel checks. The optimized trace
path additionally passed 65 broader positives (cuts, scalability, signed/zero
constant division and known numerator values) and rejected all 16 associated
false controls. No compiler timeout was increased. SMTCoq's inherited 52-name
primitive-integer/proof-irrelevance baseline remains; this is not an axiom-free
implementation.
