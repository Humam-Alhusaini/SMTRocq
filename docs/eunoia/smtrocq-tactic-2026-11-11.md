# A compiled SMTCoq certificate tactic

```coq
From SMTCoq Require Import SMTRocq.
From Stdlib Require Import ZArith.
Local Open Scope Z_scope.

Goal forall x y : Z, x <= y -> y < x + 1 -> x = y.
Proof. smtrocq. Qed.
```

`smtrocq` uses CVC5's Eunoia output as untrusted proof-compiler input. It emits
compact semantic certificates checked with the existing verified SMTCoq EUF,
LIA and Boolean operations. The resulting theorem still passes Rocq's kernel.
The lean `SMTRocq` import provides the production tactics without loading the
large optional signature-interpreter experiments. The existing `SMTCoq` import
retains those experiments and the legacy tactics.

## Two different checking contracts

`smtrocq` certifies the actual Rocq theorem from its actual hypotheses. Its
certificate format contains model tables, ordered root claims, clause steps,
scopes and verified local/theory evidence. It checks model typing, literal and
slot bounds, fresh destinations, live reads, scope discharge, final conflict,
and every submitted semantic step and cache entry, including unused entries.
The final proof also binds the reified model to the original Boolean goal and
the actual supplied hypothesis proofs. Neither an UNSAT answer nor native
candidate generation counts as evidence.

`cvc5_eunoia` additionally certifies the original CPC derivation using the
signature-generated evaluator and exact source bindings. Its strict contract
is retained. The standalone checker still provides that contract independently.
The fast compiler does **not** claim CPC source-format conformance. It may prune
unused solver work or replace a derivation with a shorter verified certificate;
the submitted certificate is checked in full. This is the untrusted-translation
boundary used by SMTCoq, rather than an optimization claim about the full CPC
interpreter.

The semantic checker is proved in `EunoiaCertificate.v` from the existing scoped
checker and concrete SMTCoq certificate gates. No new semantic axiom or admitted
proof is introduced. SMTCoq's inherited UInt63 and proof-irrelevance assumptions
remain part of the documented baseline.

## Compilation and scope

The fast compiler exports candidate solver syntax and reads generated symbol
metadata natively, rather than executing a Rocq interpreter for those producer
operations. The kernel checker independently validates the resulting semantic
certificate and its binding to the goal. Incorrect native translation can cause
rejection; it cannot authorize a false theorem.

Small arithmetic implications can be compressed to a single Micromega
certificate on the complete actual root vector. Compression uses the existing
SMTCoq arithmetic producer/checker and is bounded by 64 Boolean node visits and
12 atom occurrences. Larger or mixed inputs retain the normal CVC5 translation.
CVC5 is still invoked and its proof output parsed. Compression is an untrusted
proof-size optimization, not a trusted arithmetic answer.

UF/CNF goals over built-in sorts can also use one checked local program for the
complete root vector. Its producer propagates existing unit clauses through
newly generated clauses immediately, emitting ordinary resolution commands.
This avoids generating irrelevant congruences before a transitivity clause can
close a Boolean equality chain. Each emitted command is checked by the existing
local gate. The producer screens arithmetic and deep function graphs before
search; it is bounded by depth 4, 64 terms, 128 formulas, 1,024 clause slots,
4,096 resolution pairs and eight theory rounds. Larger inputs and failed
candidates retain the normal CVC5 translation. Abstract carriers retain the
per-step path, preserving their existing universe handling.

Coverage includes UF with multiple sorts, Boolean and mixed UF/LIA goals,
integer cuts/parity, explicit proved facts, and the existing supported Rocq
integer-division/modulo facts. Unsupported theories and unrestricted quantified
facts are outside the present scope. This is a substantial UF/LIA tactic, not a
claim of complete SMT-LIB support.

## Verification

The full install and regression build passed, including 100 native witness
cases and 34 compact theory-candidate checks by the typed Rocq gate. Seventeen
semantic checker examples cover incorrect roots, injected claims, invalid
models, missing/unused invalid certificates, fresh writes, bounds, validation
after conflict and attempts to leak a local conflict from satisfiable roots.
Nine dedicated public examples include polymorphic UF, mixed reasoning, signed
arithmetic, division, explicit facts, false-goal rejection and the formerly slow
Boolean equality chain.

All nine fresh integration/public replay modules passed compilation and a
separate recursive kernel check. The expanded assumption audit passed all
**458 targets** with no additional assumptions beyond the inherited 52-name
baseline; its separate recursive kernel replay also passed. The standalone
extraction matches all 135 proof/signature files and passed its full build,
259-target audit and sixteen fresh component/kernel replays. The native compiler
and public tactic remain upstream.

[Exact validation, commands, hashes and assumption sets](smtrocq-validation-2026-11-11.json).

## Frozen measurements

Core `f36d57e49dc068b9eaa6dc9661c5e208317a0771` was measured without
concurrent builds, audits or other test jobs. All checker source and installed
proof/native-plugin fingerprints stayed identical throughout the run. Every
backend used the same lean `SMTRocq` import. Four separate standard rounds varied
backend order. Compact theory production used its normal defaults: enabled for
`smtrocq`, disabled for strict `cvc5_eunoia`. Other optional interpreter
experiments were disabled. CVC5 retained its pinned eager/complete/no-trust flags.

The table sums each case's median **full tactic plus `Qed` wall time** over four
rounds. It includes preprocessing, CVC5/veriT, proof translation and checking;
compiler startup, imports and final file processing are recorded separately.

| Standard workload | veriT | smtrocq | Strict CPC |
| --- | ---: | ---: | ---: |
| UF, 12 cases | 1.7225 s | 1.1600 s | 4.4290 s |
| LIA, 6 cases | 0.7860 s | 0.3890 s | 4.5370 s |
| Total | 2.5085 s | 1.5490 s | 8.9660 s |

This is **38.3% less proof-construction time than veriT** (1.62 times faster)
and 5.79 times faster than strict CPC validation on this workload. UF takes
32.7% less time and LIA 50.5% less time than the corresponding veriT controls.
All 216 standard positive attempts and 24 false-goal rejection attempts passed.

The separate scaling suite passed all 21 cases twice with `smtrocq`. veriT
passed 18 cases twice and rejected the certificates for all three inequality
cycles in both rounds. On the eighteen common successes, summed per-case medians
were **2.0555 s versus 4.1545 s**, a 2.02-times speedup. Failures remain in the
coverage denominator and are not assigned artificial successful latencies.

The deeper graph suite also passed every `smtrocq` case and false control in both
rounds. Nested UF at depth 40 took a median **0.460 s versus 1.255 s** for veriT.
The 64-link propositional chain took a median **1.192 s** for tactic plus `Qed`;
veriT exceeded the 30-second whole-compiler limit in both attempts. Its inequality
cycle again failed veriT certificate checking and remains in the results.

The extended integer-cut, division/modulo and known-value manifests passed all
44 positive cases and sixteen false controls. Those division results include
proved Rocq-specific facts; baseline tactics were not given those additional
facts, so no matched division-speed claim is made. Across all final manifests,
`smtrocq` passed 174 positive attempts and 28 false controls, with repeated cases
counted as attempts rather than distinct problems.

The initial checkpoint exposed a 6.363-second Boolean equality-chain bottleneck.
After whole-goal UF/CNF compression, its final two-run median is **0.0795 s**,
versus 0.1645 s for veriT. The producer now closes the checked transitivity and
resolution proof before constructing irrelevant congruence candidates.
[All initial results, including the slow cases](smtrocq-initial-measurements-2026-11-11.json)
are retained separately.

### Remaining performance limits

Whole fresh-compiler process medians tell a different story: summing the eighteen
per-case medians gives **53.770 s for `smtrocq` versus 51.100 s for veriT**, about
5.2% slower. These processes include the wrapper, Dune, Rocq startup, imports,
assumption printing, serialization and finalization in addition to tactic and
`Qed`. The residual overhead has not been attributed to a particular phase.
The measured gain is proof-construction speed, not a claim that fresh-file
compilation is faster. Larger files may amortize startup, but that was not
measured here.

These fixed regression/scaling suites establish a substantial tested UF/LIA
fragment, not a representative SMT-LIB difficulty distribution or universal
superiority. Some individual cases still favor veriT. Compiler benchmarks retain
30-second deadlines; independent audits and recursive kernel checks use separate
900-second deadlines. Every row, failure, source/artifact hash, assumption set,
process time and command is in the [measurement record](smtrocq-measurements-2026-11-11.json).

A comparison can be reproduced after building `@install` and the native libraries:

```sh
python3 -B benchmarks/eunoia/run.py --skip-build --entrypoint SMTRocq \
  --backends verit cvc5_eunoia smtrocq --repeat 4 --timeout 30 \
  --output /tmp/smtrocq-comparison
```

The exact four separate backend orders and extension manifests used above are
recorded in the measurement artifact. Keep checker sources and installed
artifacts fixed, and run performance measurements separately from validation.
