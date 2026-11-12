# Opaque arithmetic proof in integer-map comparison

`PArray.IntOrderedType.compare` previously carried an inline `lia` proof in its
transparent greater-than branch. Rocq's VM evaluated that proof during integer
map operations. Moving the identical justification into `compare_gt`, closed
with `Qed`, removes this repeated computation. The two Boolean tests, comparison
constructors, array representation and checker interfaces are unchanged.

This is a shared SMTCoq infrastructure improvement. It accelerates veriT's
checker too. Complete generated Eunoia source checking, semantic certificates,
scopes, bindings and corruption rejection retain their existing definitions.
No native result is accepted in place of a proof.

## Isolating the cause

A probe compares `Map.find` with a raw Boolean traversal, with a proved exact
lookup refinement for every raw tree. A fixed 1,024-entry map is read 30 times
per timed phase, twice per implementation in a fresh compiler process. Keeping
the repeated warm phase distinguishes per-lookup work from one-time VM setup.
The compiler has the same 30-second deadline as the public benchmarks.

| Implementation | First reference scan | Repeated reference scan | Repeated Boolean scan |
| --- | ---: | ---: | ---: |
| Inline arithmetic proof | 4.271 s | 3.680 s | 0.015 s |
| Opaque arithmetic proof | 0.200 s | 0.030 s | 0.013 s |

These are component diagnostics; the 123-fold warm lookup difference is not a
full-tactic speedup. The accepted implementation retains the original map
implementation and changes only proof opacity.

## Complete tactic measurements

An old-library/new-library/new-library/old-library sequence uses an immutable
snapshot of the 177 old Rocq libraries and one unchanged set of four native
plugins. Explicit `-Q` paths select the actual libraries for compilation and
assumption auditing. Every selected `.vo` and native plugin is fingerprinted;
all switches retain production defaults, including printed source conclusions,
automatic indexed model encoding and adaptive checked certificates. Optional
direct certificates and compiled/indexed helper paths remain disabled.

Each reported proof time includes both `Time tactic` and `Time Qed`; compiler
startup/import time is recorded separately. Both veriT and Eunoia use the same
library variant within a round. All scheduled rows, controls, commands,
workloads, fingerprints and the small experiment wrappers are retained in
[the measurement artifact](opaque-array-comparison-2026-11-09.json).

The seven-case diagnostic comparison produced 28 accepted, audited proofs and
four successful corruption/false-goal control groups. Medians of two samples
per implementation follow; this small sample establishes a direction and does
not establish overall parity.

| Case | Previous Eunoia tactic + Qed | Updated Eunoia tactic + Qed | Updated veriT tactic + Qed |
| --- | ---: | ---: | ---: |
| Small UF congruence | 0.419 s | 0.372 s | — |
| Disjunctive LIA bounds | 3.839 s | 1.226 s | 0.138 s |
| Inconsistent LIA bounds | 2.517 s | 1.565 s | 0.176 s |
| Nested UF, depth 40 | 3.145 s | 1.325 s | 1.295 s |

Eunoia and veriT are close on this nested-UF diagnostic. Eunoia remains around
nine times slower on these LIA diagnostics. The inconsistent-bounds candidate
samples range from 1.150 to 1.979 seconds, so its median needs particular care.
The separate standard workload run below covers smaller UF/LIA goals.

The separate standard comparison ran the unchanged 20-case workload against
both backends in four rounds: **144 positive proofs and 16 false-goal
rejections**, all successful, with no timeout or new assumption. Every round
passed its source/artifact integrity check. The following values sum the
per-case medians for the 18 positive goals; they are not wall times for a single
compiler process or solver-only measurements.

| Standard workload | Previous Eunoia | Updated Eunoia | Updated veriT |
| --- | ---: | ---: | ---: |
| 12 UF cases | 7.923 s | 5.243 s | 1.755 s |
| 6 LIA cases | 9.798 s | 4.700 s | 0.822 s |
| All 18 positives | 17.721 s | 9.942 s | 2.577 s |

Eunoia improves by 44% over this combined proof-construction workload. Its
remaining gap is about 3.0 times on UF and 5.7 times on LIA. These ordinary UF
cases are smaller than the depth-40 diagnostic, which explains why closeness
on that diagnostic does not establish parity on the broader suite.

## Follow-up experiments

After the comparator fix, the earlier dynamic-interning and query-cache
experiments were recompiled before retesting. Dynamic interning's previous
large slowdown mostly disappeared, confirming that it too was affected by the
map comparator. It still took about 20–23% longer in repeated UF/LIA source
computation. These captured-source tests do not establish semantic acceptance
or predict complete tactic latency; the prototype is not selected in production.

The generic proved query cache was also retested in a complete-tactic
reference/cache/cache/reference sequence, with indexed model encoding forced
for both paths to isolate the query change. All 16 positive rows and four
control groups passed. Tactic-plus-`Qed` changes were +2.7% for small UF,
−5.3% for disjunctive LIA, −4.5% for inconsistent LIA and −1.3% for nested UF.
That result does not justify another default path or a broad speedup claim.
The temporary backend hook was removed. All four restored native plugin hashes
match those used in the main comparison.

## Validation

Both repositories passed their complete install build and regression suite.
The expanded main **373-target** assumption audit and independent recursive
kernel check passed; the standalone **194-target** audit and four fresh
component proofs with recursive kernel replay also passed. The new arithmetic
lemma introduces no assumption beyond the inherited SMTCoq UInt63 baseline.
No axiom or admitted proof was added. All 131 standalone proof/signature files
match upstream core commit `8089e667c4ad1e618d41d6e2d794ab8f82a8239c`.

[Exact validation commands and audit records](opaque-array-validation-2026-11-09.json)
are separate from the frozen timing artifact. Audits and recursive checks had
their independent 900-second deadline; benchmark compilers retained 30 seconds.
