# Checked transparent trace data

The default declares the exact complete input trace as a private
transparent definition before proving checker acceptance. The checker and its
correctness application then reference that definition instead of repeating
the large inline term. `EUNOIA_TRACE_CONSTANTS=0` restores inline trace data.

Only typed input data is shared. Every source step, its order, scopes, roots,
source computation and semantic certificate gate remains part of checking.
The definition does not assert that the trace is valid and does not cache a
Boolean verdict. Both checker evaluation and its correctness proof use the
same definition. Ordinary refutation-building APIs retain their existing path.

On the pinned Rocq runtime, Abstract's transparent private declaration calls
`Safe_typing.add_private_constant` and `Constant_typing.infer_definition`
synchronously before its continuation. The new controls require a valid data
value to reduce transparently and reject illtyped data before the callback.
Both controls are closed and passed independent kernel checking. Helper-type
checking and checked universe-context synchronization remain in place.

This optimization targets repeated typing of large trace terms. The checks
and matched measurements below support its default promotion. Diagnostic
timings are separate from the frozen performance comparison.

## Matched tactic result

Frozen commit `4d605f9` ran the standard workload in reference/shared/shared/
reference order, with identical checker sources/artifacts and only the trace
sharing flag changed. Optimized proof acceptance, printed conclusions and
adaptive certificate sharing were enabled in both paths; other experimental
evaluators were disabled and the compiler timeout remained 30 seconds.
Each path/backend proved all 36 positives and rejected all four false controls.

CVC5/Eunoia tactic totals decreased from **37.767 s to 30.330 s (19.7%)**.
`Qed` decreased from **2.168 s to 1.079 s**, giving **39.935 s versus 31.409 s
(21.4% less)** combined. The veriT tactic control was 3.194/3.031 s (`Qed`:
1.263/1.245 s). Small samples and control variation limit precision; the
optimized backend remains about 10 times slower than veriT on tactic time.
[Exact rows and hashes](trace-data-comparison-2026-11-05.json) retain the result.

The full build/regression, **308-target** assumption audit, recursive kernel
check and 19 fresh evaluator/public fixture groups passed. The two new data
boundary controls are closed. The optimized path also passed all 65 extension positives and rejected all 16
false controls: 12 cuts, 21 scalability cases, 27 constant-division cases and
five known-value cases. Including the two standard rounds, that is 101 optimized
positive attempts and 20 rejected false controls. Workload/artifact integrity
checks passed and compiler timeouts stayed at 30 seconds. These coverage runs
overlapped standalone validation and are not comparative performance claims.
[Extension rows and hashes](trace-data-extensions-2026-11-05.json) retain them.
The validated path is now enabled by default.
