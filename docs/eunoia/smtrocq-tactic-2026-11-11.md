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

Coverage includes UF with multiple sorts, Boolean and mixed UF/LIA goals,
integer cuts/parity, explicit proved facts, and the existing supported Rocq
integer-division/modulo facts. Unsupported theories and unrestricted quantified
facts are outside the present scope. This is a substantial UF/LIA tactic, not a
claim of complete SMT-LIB support.

## Verification and measurements

The full build and regression suite passed. The new semantic mutation fixtures
cover incorrect roots, injected claims, invalid models, missing/unused invalid
certificates, fresh writes, bounds, and attempts to leak a local conflict from
satisfiable roots. Dedicated public examples include false-goal rejection,
polymorphic UF, mixed reasoning, signed arithmetic, division, and explicit facts.

The comprehensive fresh replay, repeated performance comparison, expanded
assumption audit and independent kernel replay are being recorded separately.
Preliminary smoke timings are not the final performance claim.
