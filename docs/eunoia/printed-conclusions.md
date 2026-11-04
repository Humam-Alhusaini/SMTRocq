# Printed CPC conclusions as untrusted producer hints

The integrated tactic uses printed CPC conclusions as untrusted producer hints
by default. `EUNOIA_DECLARED_CONCLUSIONS=0` restores producer computation;
`=1` explicitly enables the default path.
It asks pinned CVC5 to print every CPC step's conclusion and uses those terms
as candidate syntax during native elaboration. The default was promoted after
the matched diagnostic preserved every success and rejection and consistently
reduced tactic time.

This removes a duplicate producer evaluation; it changes no source-rule
acceptance condition. The final applied checker still runs generated CPC
computation for every step, checks exact ordered premise/result bindings and
checks the local semantic certificate. Unused steps and steps after a conflict
remain in the trace. Solver proof checking, the no-trust setting, signature
selection, fuel and resource limits are unchanged.

The general elaborator API remains strict by default. Its optional
`use_declared` mode supplies candidates only: callers must independently check
the entire returned trace. Steps without a printed conclusion use the existing
derivation callbacks. Declaration/root matching, scope liveness, one-endpoint
discharge, metadata admission and expansion limits still apply in both modes.

Two corruption regressions make the distinction concrete. An unused step after
a conflict claims a valid Boolean reflexive equality but uses an unsupported
rule; another claims that equality using `refl` on a different argument, whose
actual conclusion is also valid. A later checked step restores `false` as the
final result. Both candidates must reject, even though their claimed clauses
are semantically valid. This specifically tests generated source checking.

The mode replay driver additionally checks all public UF, Boolean-UF,
purification, LIA, integer-cast and division fixtures under this switch, with
fresh compiler processes and independent kernel checking.

For a matched comparison, freeze the implementation and artifacts, set
`EUNOIA_HELPER_CACHE=0`, and alternate `EUNOIA_DECLARED_CONCLUSIONS=0|1` using
`benchmarks/eunoia/run.py`. The harness records both switches. Helper mining
runs only when the producer needs a derivation callback; printed steps do not
populate the optional helper cache. Compare these optimizations separately.

## Frozen diagnostic

Implementation `46c954b` passed the repository regression tests, install build,
226-target assumption audit and recursive kernel checking. Printed-conclusion
mode additionally passed all nine actual integration/public fixtures, including
the source-invalid but semantically valid unused-step mutations.

A seven-case workload ran in reference/helpers/conclusions/conclusions/helpers/
reference order, with identical source/artifact fingerprints and a 30-second
whole-compiler timeout. Each mode checked 10/10 positive attempts and rejected
all four scheduled false controls. Tactic totals over two rounds were 34.916 s
for reference evaluation, 32.479 s with printed conclusions and 45.363 s with
helper sharing. This is a modest focused improvement, not an overall
competitiveness result. A broader regression/comparison is required when changing this default.

[Exact rows and artifact hashes](producer-comparison-2026-11-04.json) preserve
these results independently of later changes.

## Broader default validation

At `f8f7b36`, the full build, regression suite, 239-target assumption audit and
recursive kernel check passed. The unchanged standard benchmark ran in
strict/default/default/strict order with a 30-second whole-compiler timeout.
Each run proved all 18 positive cases and rejected both false controls with
both backends. Over two rounds, CVC5 tactic totals were 65.122 s for strict
production and 59.870 s for printed conclusions; veriT control totals were
3.136 s and 2.950 s respectively. The control variation and small sample limit
the precision of this comparison; the backend remains substantially slower
than veriT on this workload.

The default additionally passed all 12 integer-cut, 21 scalability, 27 division
and five known-value cases, rejecting all 16 associated false controls. Across
the default standard rounds and extensions, that is 101 successful positive
attempts and 20 rejected false controls, with intact source/artifact checks.
Division coverage includes proved arithmetic facts supplied to the backend.

[Complete rows, command status and artifact hashes](verified-default-benchmarks-2026-11-04.json)
record these runs separately from later optimization experiments.
