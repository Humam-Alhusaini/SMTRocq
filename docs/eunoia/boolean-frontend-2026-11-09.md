# Direct, proof-producing Boolean preprocessing

The public `cvc5_eunoia` tactic now builds Boolean reflection proofs directly
for supported propositions. It retains the existing Trakt preprocessing as a
fallback. The generated Eunoia rule interpreter, semantic certificates and
source/scoping checker are unchanged.

The previous path performed general context transformations before invoking
the backend. A 64-link equality-chain diagnostic spent about 21–24 seconds in
the tactic, with most of that time before backend preparation. Native witness
generation accounted for only about 0.03 seconds. The direct prototype checked
the same goal in about 4.9 seconds; these exploratory samples motivated the
separate frozen comparison below.

## Proof boundary and fallback

`EunoiaFrontend` constructs an equivalence `P <-> b = true` for each supported
proposition, using six proved reflection lemmas and existing SMTCoq/standard
library reflection facts. It converts each actual hypothesis with the forward
direction and the goal with the backward direction. The Boolean backend then
checks the complete solver proof as before.

The translation handles Boolean equality, integer equality/order, logical
connectives and equality over carriers with a comparison instance already in
the local context. Missing instances, unsupported propositions or a failed
direct attempt return to the original preprocessing. Explicit supplied facts
retain their original context and preprocessing. The fallback regression uses
`list Z`, whose comparison instance the legacy path supplies. Compound
implications, Boolean equivalence/negation, false injectivity and supplied
facts have fresh end-to-end regressions.

An initial regression caught an unsupported-input signal that did not
backtrack. It now uses a logical tactic failure. Separate nat/cast examples
were checked against the original path and also failed there; they establish
no additional coverage and are not used as successful fallback tests.

The direct branch passes the converted goal to the pinned CVC5 backend and
its complete signature-generated source and semantic checks. No accepted Boolean result is
cached, no source inference is removed and no theory rule is added by this
front-end change. The reflection lemmas are constructive proofs; the inherited
SMTCoq assumption baseline remains separate.

## Comparison protocol

The comparison uses legacy/direct/direct/legacy order on the same compiled
libraries and native plugins. The internal tactic parameter selects the old
preprocessing body for reference runs. Both backends retain automatic indexed
model encoding, printed source conclusions and the adaptive certificate cache.
Experimental direct certificates/helper compilation remain disabled.

The unchanged standard workload contains 18 positive UF/LIA goals and two false
controls, tested against both Eunoia and veriT in each round. Separate diagnostics
include the larger equality chain. Every scheduled result, including failures
and timeouts, is retained. Positive proofs require fresh `Qed` and assumption
checks; corruption/false-goal controls run in each diagnostic round.

Proof-construction time includes both the tactic and `Qed`. Fresh compiler
wall time is separate. Every compiler has a 30-second deadline; independent
assumption and recursive kernel validation have separate 900-second deadlines.
The previous [integer-map improvement](opaque-array-comparison-2026-11-09.md)
is already present for both backends and both preprocessing paths in this
comparison. Its earlier percentages must not be added to these measurements.

The standalone checker excludes tactic preprocessing, so its component
benchmarks do not measure this front-end optimization.

## Frozen results

All **144 standard positive attempts**, **16 false-goal rejections**, **32
positive diagnostic attempts** and four corruption/false-goal control groups
passed. Source, native-plugin and front-end proof-library fingerprints matched
across rounds. There were no compiler timeouts in this comparison.

The standard values below sum the per-case median tactic-plus-`Qed` times for
the positive cases, with two samples per path. The control column uses veriT
measurements from the direct-front-end rounds; veriT itself is unchanged.

| Standard workload | Legacy Eunoia | Direct Eunoia | veriT control |
| --- | ---: | ---: | ---: |
| 12 UF cases | 5.112 s | 4.664 s | 1.761 s |
| 6 LIA cases | 4.687 s | 4.371 s | 0.847 s |
| All 18 positives | 9.799 s | 9.035 s | 2.608 s |

The observed standard-suite reduction is **7.8%**, with remaining ratios of
about **2.65 times for UF** and **5.16 times for LIA** against the corresponding
veriT controls. These small-suite samples do not establish broad parity.

| Separate diagnostic | Legacy tactic + Qed | Direct tactic + Qed |
| --- | ---: | ---: |
| Small UF congruence | 0.360 s | 0.273 s |
| Disjunctive LIA bounds | 1.228 s | 1.232 s |
| Inconsistent LIA bounds | 1.170 s | 1.182 s |
| Nested UF, depth 40 | 1.509 s | 1.213 s |
| Equality chain, 64 links | 24.946 s | 4.560 s |

The large-chain reduction is **81.7%**, or about **5.5 times faster**, while the
two LIA diagnostics are effectively unchanged. The nested-UF veriT control took
1.352 seconds in the direct rounds; that single diagnostic does not represent
the smaller standard UF cases. The large-chain legacy samples were 23.789 and
26.102 seconds; the direct samples were 4.679 and 4.440 seconds.

[Every result, workload, command and fingerprint](boolean-frontend-measurements-2026-11-09.json)
is retained. The earlier exploratory matched veriT run on the 64-link chain
hit its 30-second whole-compiler limit; it is not presented as a successful
speed measurement or a new checker-parity result.

## Validation

The complete install build and regression suite passed after the final module
rename, including compound formulas, inferred-instance fallback, false goals
and explicit supplied facts. The **384-target** assumption audit and independent
recursive kernel check both passed. All six new reflection lemmas are closed
under the global context. No new axiom or admitted proof was introduced; the
inherited SMTCoq UInt63/proof-irrelevance baseline remains unchanged.

[Commands, source hashes and every audited target](boolean-frontend-validation-2026-11-09.json)
record the final validation at core `2e60416931f987f4515610bec3f794229f10e43a`.
The standalone checker is unchanged by this front-end work and retains its
previously validated 131-file synchronization and 194-target audit.
