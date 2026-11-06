# Signature-specialized evaluator

`EUNOIA_STAGED_PROGRAMS=1` selects an experimental source checker whose helper
bodies are specialized from the generated Eunoia program syntax. The ordinary
semantic gate, exact roots, premises, conclusions and scope checks still apply.
The switch is off by default. Helper-cache mode takes precedence if both are set.

`EoStaged.compile` structurally compiles expressions to Gallina functions while
retaining each original fuel decrement and error priority. `EoFuelLayers`
connects recursive helper calls through lazy, structurally recursive fuel
layers; it does not eagerly allocate the full fuel budget. `EoCompiledPrograms`
compiles pattern-matched helper bodies, and `CpcStaged` specializes the actual
generated signature. No list of handwritten helper rules is introduced.

The refinement theorems prove equality of complete computations, including
missing-program and stuck results, for arbitrary inputs and fuel. The surface
rule and complete-trace refinements connect this evaluator to the existing
checked backend. All new generic refinement proofs are closed; the complete
SMTCoq checker retains its documented inherited primitive assumption baseline.

A prepared table is shared across a complete trace. Scope-closing source rules
continue through the reference evaluator. Printed conclusions are untrusted
producer candidates, independently recomputed by the selected source checker.

An isolated development sample for 3,000 repeated arithmetic helper calls took
1.928 s in reference VM reduction and 1.026 s in specialized reduction; `Qed`
took 1.816 s and 1.084 s. This is an exploratory component measurement, not an
end-to-end tactic result. Real fixture and matched tactic measurements are
required before changing the default.

The integrated implementation passed the full repository regression build,
install build, 254-target assumption audit, and recursive kernel checking.
The generated-source regression replays all 32 captured CPC traces through
this evaluator and checks the resulting proof modules independently.

## Matched tactic result

Frozen implementation `f1ef28e` passed all nine fresh public/integration fixture
groups and their independent kernel check. The unchanged seven-case diagnostic
then ran reference/specialized/specialized/reference, with printed conclusions
enabled in both paths, all other experimental optimizations disabled, identical
source/artifact fingerprints and a 30-second whole-compiler timeout.

Each path checked 10/10 positive attempts and rejected all four false controls.
Tactic totals were **33.420 s reference versus 39.226 s specialized**; `Qed`
totals were 0.470 s and 0.331 s. The specialized tactic was slower on every
positive case in this sample. It remains disabled by default. The earlier
helper-loop speedup does not establish a full-tactic improvement.

[Complete rows and artifact hashes](staged-comparison-2026-11-04.json) retain
the negative result. Further work must address actual full-path costs rather
than promoting this implementation on component timings.
