# Checked transparent trace data experiment

`EUNOIA_TRACE_CONSTANTS=1` declares the exact complete input trace as a private
transparent definition before proving checker acceptance. The checker and its
correctness application then reference that definition instead of repeating
the large inline term. The default remains unchanged.

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

This opt-in experiment targets repeated typing of large trace terms. It needs
full regression, corruption replays, assumption audits, and paired tactic/`Qed`
measurements before any default promotion. Diagnostic timings are not a
performance claim.
