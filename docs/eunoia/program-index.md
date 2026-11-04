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
