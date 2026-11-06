# Indexed signature aliases

The generated CPC interface precomputes indexes for canonical and surface
symbol aliases. The rule interpreter, semantic gate, fuel bounds, source-step
validation and supported signature fragment are unchanged.

`EoRename.refinement` proves, for every alias table and term, that indexed
renaming equals the original ordered association-list renaming. Generated
pointwise lemmas instantiate that result for both signature tables. All source
wrappers use the same canonicalization functions, including helper-cache,
program-index, staged and direct evaluators. No function-extensionality axiom
is required; the new renaming proofs are closed.

The implementation passed the full repository regression and install build,
288-target assumption audit, independent kernel checks, 28 common native
fixture groups across all seven evaluator modes, and five further public
direct-mode groups. Python compiler validation passed all 48 tests. Source
regressions retain all 32 captured CPC traces and corruption controls.

An isolated development diagnostic improved repeated complete-rule computation,
but no tactic-level speedup is claimed until old/new frozen revisions have been
compared on the same goals, hardware, solver settings and compiler timeout.

## Paired tactic result

Frozen revisions `67cc9a3` (association lists) and `ccce9a4` (indexed aliases)
ran the unchanged standard workload in old/new/new/old order, with both veriT
and CVC5/Eunoia, printed conclusions enabled and all other experimental paths
disabled. Each version/backend proved all 36 positive attempts and rejected all
four false controls over two rounds. Compiler timeout stayed at 30 seconds.

CVC5/Eunoia tactic totals decreased from **59.492 s to 56.726 s** (about 4.6%).
The veriT control was nearly unchanged, **3.145 s versus 3.130 s**. `Qed` totals
were 2.033/1.889 s for CVC5/Eunoia and 1.624/1.345 s for veriT. These are small
samples; the backend remains about 18 times slower than veriT on this workload.

Source/artifact fingerprints differ intentionally between the two revisions
and were verified stable within each revision; workload hashes matched across
all four runs. [Rows and artifact hashes](alias-index-comparison-2026-11-05.json)
retain the evidence. Broader arithmetic regression results are recorded
separately.

The indexed default subsequently passed all 65 extension positives: 12 integer
cuts, 21 scalability cases, 27 constant-division cases and five known-value
cases. All 16 associated false controls rejected, with intact workload/artifact
integrity checks and unchanged 30-second compiler timeouts. Including the two
standard rounds, the optimized path checked 101 positive attempts and rejected
20 false controls. Division supplies additional proved facts and is not an
equal-support comparison with veriT.
[Extension rows and hashes](alias-index-extensions-2026-11-05.json) retain these
regression results separately from the paired standard-workload comparison.
