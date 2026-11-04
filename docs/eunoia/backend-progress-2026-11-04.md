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
27 positive division regressions and eight false controls. These use actual
standard-library proofs as bound roots in the existing UF/LIA semantics.
Native arithmetic candidates now preserve the verified builder's association,
branch numbering and Boolean connective shapes, without interning extra
proof-only Boolean expansions. A bounded Boolean resolution prefix avoids
unnecessary arithmetic search; its zero-budget regression exercises the actual
arithmetic certificate path. All 98 native witness cases and mutations run
against the production gate in routine tests.

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
