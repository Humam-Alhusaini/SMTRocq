# Direct signature-program compilation

`EUNOIA_DIRECT_PROGRAMS=1` selects an experimental source evaluator. It is off
by default. The native backend keeps its normal adaptive certificate sharing:
flat, unshared scoped and shared traces each have a proved adapter. Helper-cache
mode takes precedence if enabled simultaneously.

The generator reads the same pinned Eunoia signature and selected helper closure
as `CpcGenerated`. It emits structurally recursive Gallina functions, resolves
helper calls statically, and orders dependency components before their callers.
Programs with more than 32 cases use the original reference interpreter. This
resource policy currently compiles 58 helpers and retains the 78-case evaluator
as a reference fallback; it changes implementation selection, not rule coverage.

Each compiled helper has a kernel-checked defining equation and correspondence
to its original generated body. Strong induction on fuel proves exact dispatch
refinement for every name, argument vector and fuel value, including missing
programs and stuck computations. A separately proved entry specialization removes
construction of a dispatch list at runtime. The surface-rule and complete-checker
proofs transport these results to the existing SMTCoq semantic gate. Generic
proofs are closed; complete checker proofs retain the documented inherited
primitive-integer/proof-irrelevance baseline.

```sh
python3 tools/eunoia/generate_direct.py --output /tmp/CpcDirect.v \
  --manifest /tmp/cpc-direct-manifest.json
```

The regression script regenerates and compares both files, replays all 32 CPC
captures, and independently checks their kernels. Native replay modes include
`Direct`, `DirectShared`, and `DirectReference`; the latter two explicitly exercise
the alternative representation selections.

An exploratory complete-rule component sample included pattern checks, typing,
surface conversion and generated evaluation for `arith_poly_norm` on
`x + 0 = x`. For 3,000 calls, VM reduction took 3.647 s reference and 3.325 s
direct; `Qed` took 3.740 s and 3.405 s. Both fresh proofs were closed and passed
independent kernel checking. This single diagnostic is not a full-tactic or
cross-prover performance result. Matched tactic measurements are required before
changing the default.

The integrated snapshot passed the full repository regression build, install
build, expanded 285-target assumption audit, and recursive kernel checking.
Native replay validation covers normal adaptive selection plus forced shared
and forced reference selection before matched tactic timing.

## Matched tactic result

At frozen implementation `67cc9a3`, all 17 native fixture groups passed: nine
normal direct groups plus four each with forced sharing and forced reference
representation. Their independent kernel check also passed.

The unchanged seven-case diagnostic then ran reference/direct/direct/reference
with printed conclusions enabled, other experimental optimizations disabled,
normal adaptive sharing preserved, identical source/artifact fingerprints and
a 30-second whole-compiler timeout. Both paths checked 10/10 positive attempts
and rejected all four false controls. Tactic totals were **32.552 s reference
versus 35.044 s direct**; `Qed` totals were 0.453 s and 0.477 s.

The direct path remains disabled by default. Its modest complete-rule component
gain did not transfer to this tactic workload.
[Complete rows and artifact hashes](direct-comparison-2026-11-04.json) retain
the negative result independently of later optimizations.
