# Verified program-name indexing

`EUNOIA_PROGRAM_INDEX=1` enables an experimental source interpreter whose
helper lookup uses a precomputed string trie. It is disabled by default while
full tactic measurements are pending.

The index is computed directly from `CpcGenerated.cpc_programs`. No program or
rule table is handwritten. `EoNameIndex.lookup_from_list` proves equality with
the original first-match list lookup for every string, including missing keys,
empty keys and duplicate keys. The index is immutable and contains signature
data, never results supplied by a proof.

`EoIndexed.evaluate_indexed_refinement` proves equality of the full computation
with the reference interpreter for arbitrary fuel, environments, type queries
and primitive hooks when the lookups agree. The generated-CPC wrappers and
`EunoiaProgramIndex.checker_refinement` transport that result to the existing
trace checker. Fuel exhaustion and failed source derivations cannot become
successful through indexing.

The final checker still evaluates every source step, checks ordered bindings,
checks scoped discharge and validates every local semantic certificate. Scope
closing rules currently use the reference source evaluator. The native producer
can also use indexed derivation when a conclusion has not been printed.

For comparisons set `EUNOIA_HELPER_CACHE=0`, freeze sources/artifacts, and vary
`EUNOIA_PROGRAM_INDEX=0|1` independently of `EUNOIA_DECLARED_CONCLUSIONS=0|1`.
Both switches are recorded by the benchmark harness. A populated experimental
helper cache takes precedence over the indexed trace representation, so the
optimizations should be compared separately.

## Frozen trie-only experiment

Implementation `389a044` passed all nine indexed public/integration replays,
repository regressions, the install build, and its expanded assumption/kernel
audit. Eight serial matched rounds preserved 10/10 positives and all four
false controls per configuration. Total tactic times were 35.296 s reference,
40.548 s indexed, 32.287 s printed conclusions, and 37.949 s combined.
Indexing is therefore not enabled by default.

[Exact rows and hashes](program-index-comparison-2026-11-04.json) retain the
experiment. An isolated cycle profile located the regression in checked
acceptance/reduction; forcing the same certificate representation did not
remove it. A short-prefix/trie hybrid was also rejected after its focused
diagnostic failed to improve that cost.

## Separating lookup from representation

The initial native index option forced the shared-certificate representation.
Consequently its earlier full-tactic comparison measured both program lookup
and that representation choice. The historical negative result remains a
measurement of the complete option at its frozen revision.

New proved flat and scoped adapters let the native emitter preserve its normal
adaptive sharing policy when program indexing is enabled. Their correctness
transports acceptance to the existing checkers using the exact indexed-source
refinement theorem; source replay, semantic gates and scope/root binding remain
checked. The shared adapter remains available when sharing is selected.

Fresh `IndexedAdaptive` and `IndexedReference` replay modes exercise adaptive
and forced nonshared emission; the existing `Indexed` mode forces sharing.
Program indexing remains opt-in (`EUNOIA_PROGRAM_INDEX=1`) pending a matched
comparison with the same sharing policy on both paths.

## Matched adaptive result

Frozen commit `93431c0` compared reference/indexed/indexed/reference with the
same checker sources/artifacts, optimized proof acceptance, printed conclusions,
adaptive sharing and unchanged 30-second compiler timeouts. Separate UF and
LIA probes confirmed identical sharing decisions and counts before timing.
Each path/backend proved all 36 positives and rejected all four false controls.

The indexed path remained slower: **38.319 s versus 37.232 s** of CVC5/Eunoia
tactic time (2.9% more). `Qed` was 1.956/2.112 s, giving 40.275/39.344 s combined.
The veriT control was 2.903/3.006 s. Indexing therefore remains disabled by
default. Removing the representation difference did not establish a gain.

The full build/regression, **306-target** assumption audit and recursive kernel
check passed. Six fresh shared/adaptive/nonshared integration groups and five
additional public adaptive groups passed independent kernel checking. The
initial adaptive replay exposed a missing direct import in the integration
fixture; adding the two adapter imports fixed it before these fresh checks.
[Exact rows and hashes](program-index-adaptive-comparison-2026-11-05.json)
retain the matched result.
