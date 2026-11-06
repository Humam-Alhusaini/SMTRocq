# Indexed model encoding

SMTCoq checks indexed atoms, formulas and clauses against shared tables. Its
checkers follow those indices instead of repeatedly expanding expressions into
syntax trees. The Eunoia adapter previously rebuilt overlapping Eunoia terms
recursively when populating its clause-encoding cache. Deep congruence proofs
amplify that repeated work.

`EunoiaModelDag` now walks the existing SMTCoq atom and formula tables once,
computing reusable encodings in dependency order. It reuses the adapter's type
guards, operator names, numeral encoding and SMTCoq interpretation. There is no
second SMT-LIB semantics. The finite-map cache is computed inside Rocq; the
importer supplies neither cache entries nor cached acceptance results.

Each entry records the recursive fuel needed for its result. Missing entries,
missing prerequisites, `Fnot2` nodes and insufficient fuel fall back to the
original recursive encoder. `encoding_entries_refinement` proves exact equality
with the original encoder for every table, naming, fuel and key list, including
malformed inputs. `EunoiaModelDagCheck.checker_refinement` lifts that equality to
the entire original `EunoiaMemo.checker` Boolean result.

Generated CPC rule evaluation, exact premise/conclusion bindings, roots, scopes
and every local semantic certificate remain checked. Invalid unused entries and
invalid steps after the conflict are still rejected. The trust baseline remains
SMTCoq's existing UInt63 and proof-irrelevance assumptions; no admissions or new
axioms are introduced.

`cvc5_eunoia` selects this encoder when an encoded root has at least 16 nested
applications. This performance heuristic retains the cheaper setup for small
goals. `EUNOIA_MODEL_DAG=1` forces indexed encoding and `=0` selects the original
path; unset or `=auto` uses the heuristic. Experimental helper sharing retains
its existing checker. The two model encoders are pointwise equal regardless of
the heuristic. Otherwise selected model encoding takes precedence over the
experimental specialized/direct/staged/indexed evaluators; set
`EUNOIA_MODEL_DAG=0` when measuring those evaluators separately.

## Matched result

A fixed build ran reference/auto/auto/reference with full source and semantic
checking, identical source/artifact fingerprints, and a 30-second compiler
budget. Median tactic times were:

| Nested congruence | Original encoder | Automatic encoder | Reduction |
| --- | ---: | ---: | ---: |
| Depth 20 | 1.6625 s | 1.4720 s | 11.5% |
| Depth 40 | 3.8625 s | 3.0050 s | 22.2% |

Depth-40 veriT controls were 0.832/0.801 s, so Eunoia still trails veriT by
about 3.8 times there. Summed case medians across all seven positive diagnostics
were 14.562/13.444 s (7.7% less); small cases kept the original encoder. These
two samples per path establish a bounded improvement, not general competitive
performance. The earlier exploratory 10.72/2.86 s observation was not reproduced
and is not used as the speedup claim.

Each Eunoia path proved 14/14 positive attempts and rejected all four false
controls. veriT proved its 12 common positive attempts and rejected all four
false controls; its two integer-cycle errors remain in the denominator.
[Exact rows, flags, versions and fingerprints](indexed-model-comparison-2026-11-06.json)
retain the evidence.

The fixed diagnostic workload is `benchmarks/eunoia/model-graph.json`. It includes
flat equality chains, nested congruence at depths 5/10/20/40, an eight-variable
integer cycle, and two false controls. These are scalability diagnostics, not
the original standard workload. Preserve all cases and the 30-second compiler
budget when comparing flags; veriT's failure on the integer cycle remains a
failure in the results.

Run fresh source and semantic corruption controls through the new encoder with:

```sh
python3 scripts/eunoia/check_modes.py --modes Model ModelShared ModelReference
```

`Model` retains adaptive semantic certificate sharing, `ModelShared` forces it,
and `ModelReference` uses inline certificates. All three force indexed model
encoding and retain generated source checking.

## Validation

The full install build/regression suite and expanded **360-declaration**
assumption audit passed against the inherited 52-name baseline. The final
recursive kernel pass over the audited libraries and tests also passed. Twenty-one
fresh native/public replay groups passed independent recursive kernel checking:
all three model modes covered source mutations, scopes, UF, Boolean UF,
purification, LIA and public Boolean/equality tactic entry points. Focused model
tests additionally cover low fuel, out-of-bounds indices, `Fnot2` fallback,
invalid unused certificates and bad source steps after the conflict.

The standalone extraction contains identical copies of the four new proof/test
files. Its install build/full regressions and expanded **181-declaration**
assumption audit passed. Four fresh complete-checker benchmark fixtures passed
all timing phases and recursive kernel checking. Those concurrent smoke-test
timings validate the runner and are separate from the matched tactic results.
