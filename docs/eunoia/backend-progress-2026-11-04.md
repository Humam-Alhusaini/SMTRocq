# Backend progress, 4 November 2026

This updates the [earlier checkpoint](backend-checkpoint-2026-11-04.md).
The implementation remains experimental; no Lean-SMT, Sledgehammer or Logos
performance comparison is claimed.

## Signature and live coverage

The pinned 35-file CPC closure selects 87 rules and 59 helpers, including all
50 Boolean declarations, positive/negative arithmetic scaling, integer lower/upper
tightening and the generated arithmetic trichotomy rule. Unsupported
rules fail closed. [Restricted rational intermediates](integer-embedding.md)
now support live integer parity and rounded coefficient bounds without adding
object-level Real semantics. Raw CPC terms, conditions and scoped assumptions
remain intact for generated computation; every source inference still needs
exact table binding and a local semantic certificate.

The public suites include 23 UF, 11 Boolean UF, 17 integer/mixed and 12 integer-cut
proofs, plus the purification/constant/multi-goal regressions and false/corrupted
controls. The eight-variable inequality cycle and its satisfiable non-strict
variant exercise actual hypothesis bindings.

[Proved Rocq division facts](division.md) extend the backend with signed and
zero constant division/modulo, constant shifts and nested quotients. There are
33 positive division regressions and thirteen public false controls. These use actual
standard-library proofs as bound roots in the existing UF/LIA semantics.
Native arithmetic candidates now preserve the verified builder's association,
branch numbering and Boolean connective shapes, without interning extra
proof-only Boolean expansions. A bounded Boolean resolution prefix avoids
unnecessary arithmetic search; its zero-budget regression exercises the actual
arithmetic certificate path. All 98 native witness cases and mutations run
against the production gate in routine tests.

## Boolean truth wrappers and measured ground-value improvement

The public preprocessor can wrap an integer equality as `(7 =? x) <-> true`.
Two proved Boolean truth lemmas now expose the actual proved equality before
known-value instantiation, including reversed equalities. False polarity and
arbitrary connectives are not treated as proved integer equalities. The change
passed 202 assumption targets, both checker modes with independent kernel
replay, full repository tests and the install build. Evidence:
`eunoia-mode-replay-gzbuu0o6` and `eunoia-proof-audit-8draktq6`.

At the preceding `8c95f22` checkpoint, two frozen repeats retained 54/54 division
successes and 16/16 false-control rejections, plus 10/10 known-value successes
and six rejected controls. All integrity checks passed. Division tactic totals
were 117.198 s over two repeats (58.599 s per repeat), versus 101.657 s for the
single preceding `8a5c14b` repeat. The three known-numerator cases fell from
15.576/13.329/13.757 s to two-repeat medians around 0.53/0.55/0.51 s.
The Boolean-wrapped reverse case still took 16.1–16.8 s at that checkpoint;
its subsequent wrapper fix is separately validated and requires fresh timing.
[Exact results](verified-known-values-benchmarks-2026-11-04.json) preserve the
unchanged manifests and scheduled denominators.

A separate standard native-computation experiment was rejected: matched
VM/native/native/VM rounds checked 10/10 VM positives and 8/10 native positives;
the native path timed out twice on the known-numerator case and increased
common-case latency. All four integrity checks passed. The production backend
keeps VM reduction. [Raw comparison](native-comparison-2026-11-04.json) retains
all timeouts rather than comparing unequal solved totals.

## Proved ground-value extension

Known numerator equalities now produce quotient/remainder value facts with
actual equality and ground-calculation proofs. Reversed equalities and UF
numerators are covered. The expanded implementation passed all 198 named
assumption targets, both checker modes with independent kernel replay, full
repository runtest and the install build. Evidence: `eunoia-mode-replay-gq2efr_n`,
`eunoia-proof-audit-rx6mb32o` and `eunoia-association-regression-mutation`.

The arithmetic branch-order regression uses a compound root and disables the
Boolean prefix to bypass the direct-equality shortcut. Restoring the old
left-associated native conjunction makes the verified local gate reject the
Micromega certificate at source congruence step `@p17`; restoring the fix makes
the same proof pass. The original 35-case division workload remains unchanged;
five additional known-value positives and three false controls have a separate
manifest. Fresh performance measurements follow validation.

## Verified division checkpoint at 8a5c14b

The expanded implementation passed 186 named assumption targets with no
additions to the inherited baseline, independent kernel checking, both emitter
modes, full repository runtest and the final install build. The mode replay is
`eunoia-mode-replay-8m_h_ahf`; the successful audit is
`eunoia-proof-audit-va2kmmom`. The audit runner's integration loadpath was fixed
before the successful audit and remaining repository checks.

Serial fresh-compiler benchmarks retained the same 30-second whole-compiler
limit and passed every source/artifact integrity check:

| Workload | Repeats | Eunoia checked / scheduled | veriT checked / scheduled |
| --- | ---: | ---: | ---: |
| Original regression | 2 | 36/36 | 36/36 |
| Integer cuts | 1 | 12/12 | 11/12 |
| Scalability | 1 | 21/21 | 18/21 |
| Rocq division extension | 1 | 27/27 | 1/27 |

Both backends rejected all four scheduled original controls, five integer-cut
controls and eight division controls. Scalability contains positives only.
Division uses additional proved Rocq facts in Eunoia; baseline tactics receive
their normal preprocessing. Their division results do not compare equivalent
theory support. The sole common division success is modulo congruence.

On the original workload, tactic totals were 60.968 s versus 2.706 s over two
repeats, and Qed totals were 1.714 s versus 1.077 s. Common-success tactic totals
were 25.412 s versus 0.871 s for 11 integer-cut attempts, and 35.617 s versus
2.337 s for 18 scalability attempts. The latency gap remains substantial;
small changes from d5af018 on shared hardware do not establish an improvement.

All 27 Eunoia division proofs completed, with 101.657 s total tactic time.
This extends measured coverage; it is not an overall performance claim.
[The separate machine-readable report](verified-division-benchmarks-2026-11-04.json)
retains exact counts, failures, common-success timings and artifact hashes.
Raw evidence is preserved under `_build/eunoia-evidence/eunoia-8a5c14b-*`.

## Verified checkpoint at d5af018

The frozen 85-rule/57-helper implementation passed all 133 named assumption-audit targets,
independent kernel checks, both native emitter modes, generated/corrupted proof
replays and full repository runtest. All benchmark source/artifact integrity
checks passed. The compiler timeout remained 30 seconds.

| Workload | Repeats | Eunoia checked / scheduled | veriT checked / scheduled |
| --- | ---: | ---: | ---: |
| Original regression | 2 | 36/36 | 36/36 |
| Integer-cut extension | 1 | 12/12 | 11/12 |
| Scalability diagnostics | 1 | 21/21 | 18/21 |

Both backends rejected all four scheduled standard-workload false controls and
all five integer-cut controls. The scalability manifest contains positive cases
only. Eunoia's formerly timed-out length-8 cycle now completes within the same
limit. VeriT's parity error and three cycle errors remain unsolved.

Standard-workload tactic totals over two repeats were **62.540 s** for Eunoia
and **2.642 s** for veriT; Qed totals were 2.038 s and 1.067 s. Integer-cut tactic
totals were 28.261 s on Eunoia's 12 successes and 0.908 s on veriT's 11 successes.
For the **same 11** checked cases, totals were 27.016 s and 0.908 s. Scalability
totals were 57.794 s on Eunoia's 21 successes and 2.281 s on veriT's 18 successes;
on the **same 18**, they were 36.515 s and 2.281 s. Startup/process wall time,
Qed and tactic time are distinct measurements. These samples establish coverage
and show a remaining latency gap; they do not establish overall competitiveness.

[Machine-readable results](verified-benchmarks-2026-11-04.json) retain the
scheduled counts, failure IDs, common-success comparisons and artifact hashes.
Reproduce with `benchmarks/eunoia/run.py --backends verit cvc5_eunoia --repeat 2
--timeout 30`, selecting the committed integer-cut or scalability manifest with
`--cases` for the extensions. Hardware is shared; use several rounds before
making broader performance claims.

## Measured checkpoint at 9401f76

Rocq 9.2, OCaml 4.14.2, Dune 3.21.1, pinned CVC5 1.4.2; serial fresh compilers,
one repeat, unchanged 30-second whole-compiler timeout. Every positive requires
Qed, a new artifact and a parsed baseline assumption report. Source/artifact
integrity checks passed. These are small samples on shared hardware.

| Workload | Eunoia checked positives | veriT checked positives | False controls, Eunoia / veriT |
| --- | ---: | ---: | ---: |
| Original regression | 18/18 | 18/18 | 2/2 / 2/2 rejected |
| Integer-cut extension | 12/12 | 11/12 | 5/5 / 5/5 rejected |
| Scalability diagnostics | 20/21 | 18/21 | None in this manifest |

Eunoia's standard-workload tactic total was 55.242 s, with 1.219 s in Qed;
veriT's was 1.642 s, with 0.622 s in Qed, on the same 18 successes.
Integer-cut tactic totals were 40.571 s for Eunoia's 12 successes and 1.145 s
for veriT's 11 successes; these totals have different solved sets. The latter
backend rejected the two-variable parity proof with an error. Scalability
retains Eunoia's length-8 inequality-cycle timeout and veriT's three cycle errors
in the coverage denominator. No failure is treated as a success.

A two-repeat matched five-positive/two-negative diagnostic, with a separately
reported 60-second limit, checked 10/10 positives and rejected 4/4 controls in
both versions. Total tactic time fell from 107.684 s before the lazy-query/UF
search changes to 22.547 s afterward. Equality-chain medians fell from 44.831 s
to 3.686 s. These diagnostic limits do not replace the standard 30-second result.

## What changed

- Source-literal encoding caches have pointwise refinement proofs and bounded
  source-derived keys; misses use the reference encoder.
- Recursive encoding shares the existing interpreted atom table. Its refinement
  lemmas are proved by reflexivity.
- Immutable guards are shared across source steps.
- Signature nil resolution delays type queries until their declarations need
  them. Resolver and conversion refinements preserve their results.
- Pure integer-sorted UF expressions no longer trigger expensive Micromega
  search. Interpreted atoms, including integer literals, keep LIA enabled.
  This changes untrusted candidate production; the semantic gate is unchanged.

Optional `EUNOIA_PROFILE_PHASES=1` reports preparation, certificate conversion,
private-helper checking and final goal conversion. Nested phase times must not
be added together. The benchmark records this option and the fixed solver profile.

## Checked proof-construction changes

Standard VM goal normalization inside the private proof helper avoids ordinary
reduction of the complete checker during proof elaboration. The helper still
undergoes synchronous kernel checking against its complete original type,
and the final theorem still passes exact_check and Qed.

For supplied hypotheses, a proved generic lemma transports validity from one
checked equality between the complete ordered interpreted root vector and its
actual Boolean values. Actual hypothesis proofs supply every fact; duplicates,
order and the negated-goal root are retained. No semantic result is assumed or
reused across invocations.

A focused checked trial reduced the length-8 cycle to 10.216 s of tactic time
and 0.221 s of Qed, within the standard compiler limit; all four positive cases
and both false controls behaved as expected. The complete validation subsequently passed: 133 named assumption-audit targets,
independent kernel checks, both emitter modes, corrupted/captured source tests and
full repository runtest. The frozen matched reruns are recorded in the verified checkpoint above.

Helper goal types are checked before normalization, and the reducer sees the
current checked universe context. Abstract and quantified carriers retain their
actual CompDec proofs and universe constraints.

No new axiom or admitted proof is introduced. SMTCoq's inherited 52-name
primitive-integer/proof-irrelevance assumption baseline remains. This is not an
axiom-free implementation.
