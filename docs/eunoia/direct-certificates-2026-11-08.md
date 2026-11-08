# November 8 direct-certificate checkpoint

The new direct local certificate gate is proved and available behind
`EUNOIA_DIRECT_CERTIFICATES=1`. It remains experimental and off by default.
This checkpoint does **not** establish parity with veriT or a robust overall
speedup. Full signature-generated source checking remains mandatory.

The direct gate derives the exact conclusion from the exact ordered premises
using SMTCoq's existing command executor. It avoids refuting the negated
conclusion for each inference. Bounded native search falls back to the existing
refutation producer. Both gate variants share their immutable table guard;
the original gate retains its acceptance conditions.

## Frozen comparison

The reference/direct/direct/reference sequence used four Eunoia cases and three
veriT controls, production printed conclusions, automatic indexed encoding,
and a 30-second whole-compiler deadline. All 28 positive attempts passed their
assumption checks, and each round passed the false-goal and corruption controls.
Source and native-library fingerprints matched across the four rounds.

These measurements were taken **before** factoring the immutable guard between
the two gates. They retain the measured source/artifact hashes and are not a
performance claim about the later final build. No default was promoted from
these results.

| Case | Reference tactic + Qed | Direct tactic + Qed |
| --- | ---: | ---: |
| Small UF congruence | 0.375 s | 0.445 s |
| Disjunctive LIA bounds | 3.414 s | 3.280 s |
| Inconsistent LIA bounds | 2.384 s | 2.347 s |
| Nested UF, depth 40 | 3.026 s | 3.271 s |

The small arithmetic differences did not reproduce the earlier exploratory
12% improvement convincingly. The veriT controls also varied between rounds.
The UF regression rules out enabling this mode generally on this evidence.

Timing boundaries matter: in the reference rounds, nested-UF veriT took a
median 0.776 s in the tactic and 1.054 s at Qed, versus Eunoia's 2.971 s and
0.055 s. Total construction was about 1.65 times slower there. Disjunctive LIA
remained about 16.5 times slower in total construction. Component checking,
tactic time, Qed, fresh compiler time and recursive kernel replay are distinct
measurements; these ratios do not describe the standard benchmark suite.

[Exact measurements and fingerprints](direct-certificates-benchmarks-2026-11-08.json)
include every scheduled row and control command.

## Rejected optimization trials

Additional isolated trials did not establish a large gain:

- Whole-source type-query caches, bottom-up typing caches, and caches restricted
  to repeated formulas increased setup/lookup work or were neutral.
- Fresh term identities and term fingerprints did not improve the captured
  generated-rule replays. Dynamic interning was substantially slower.
- Compact source transport and source-term lets increased complete tactic time.
- Reusing indexed model encodings for root binding had an exact Boolean
  refinement proof, but only a roughly 2% UF change in one exploratory run.
- A proved binding shortcut cached whether a model encoding normalizes to
  itself. Small single-run gains in UF and one LIA case need repetition;
  it is not enabled in production.
- A diagnostic found only 24 repeated conclusions among 330 theory commands
  in one LIA trace; caching those alone cannot remove most checking work.
- Coarser CVC5 proof granularities aborted under the unchanged eager, complete,
  no-trust settings, including with full-proof-strict. Disabling simplification
  left the sampled LIA proofs unchanged in size. Solver trust checks were kept.

No unsuccessful prototype is selected by the production tactic. The remaining
work requires reducing repeated source interpretation, typing and conversion
without dropping source steps or their semantic obligations.

## Validation

The eleven fixed direct-gate tests cover exact conclusions and premises,
invalid unused commands, true-clause fallbacks, bounds, complete scoped source
checking and a source-invalid step after a conflict. Native/public replays
include the original source and semantic corruption controls. The direct mode
passed 21 initial native/public replay groups and an initial 372-target
assumption audit with recursive kernel checking.

Final validation after sharing the immutable guard is recorded separately in
[the validation artifact](direct-certificates-validation-2026-11-08.json).
No axioms or admitted proofs were added; the inherited SMTCoq UInt63 and
proof-irrelevance baseline remains.

The profiler now builds and fingerprints the witness library's own native
plugin as well as its consumers. This prevents a stale plugin from producing
an interface mismatch after a witness interface change. It records printed
conclusion mode, explicit optimization switches and tactic-plus-Qed time.
Compiler deadlines default to 30 seconds; optional recursive kernel checking
has a separate 900-second deadline.
