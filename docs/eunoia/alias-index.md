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
