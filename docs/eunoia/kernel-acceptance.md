# Single kernel conversion experiment

`EUNOIA_SINGLE_KERNEL_ACCEPTANCE=1` constructs a VM-cast proof body inside
`Abstract.cache_term_by_tactic_then`, avoiding the preceding VM goal reduction.
The default retains the existing reduction and `exact_check` path. Helpers
whose types require ordinary proof checking rather than normalization retain
`exact_check` in both modes.

The proof body is accepted only when Rocq's private declaration synchronously
kernel-checks it against the complete original type. On the pinned Rocq 9.2
runtime, `Subproof.declare_abstract` pushes the side effect through
`Evd.push_side_effects`, `Safe_typing.add_private_constant`,
`infer_direct_opaque` and `Constant_typing.check_delayed` before Abstract calls
its continuation. The initial helper-type check and checked universe-constraint
synchronization remain in place. The tactic does not defer this check to `Qed`.

The direct cast constructor is intentionally confined to that checked private
declaration boundary. It must never expose an unchecked body to the caller.
`tools/eunoia-kernel-acceptance-probe/Controls.v` checks an accepted helper and
an invalid helper; a mutable callback marker detects whether an invalid proof
reaches the continuation even if later checking would reject it. Both control
theorems are closed and independently checked by the kernel.

This is an experimental proof-construction optimization, with no change to
signature-generated rules, source replay, semantic checking, roots or permitted
assumptions. It needs paired tactic and `Qed` measurements and the full native
corruption suite before any decision to change the default.

## Matched tactic result

Frozen commit `8e1f30a` ran the standard workload in reference/new/new/reference
order. Every round used the same source and proof/plugin artifacts, printed
conclusions, adaptive certificate sharing and a 30-second compiler timeout.
Only `EUNOIA_SINGLE_KERNEL_ACCEPTANCE` differed. Each mode/backend proved all
36 positive attempts and rejected all four false controls over two rounds.

CVC5/Eunoia tactic totals fell from **52.370 s to 35.516 s (32.2%)**. `Qed`
totals increased from **1.704 s to 2.086 s**; combined tactic/`Qed` time still
fell from **54.074 s to 37.602 s (30.5%)**. The veriT tactic control was
**2.878 s versus 3.025 s** (`Qed`: 1.204/1.165 s). Control variation and small
samples limit precision. The new path remains about 12 times slower than
veriT on tactic time in this workload.

[Exact rows and artifact hashes](kernel-acceptance-comparison-2026-11-05.json)
retain the comparison. All 33 fresh native fixture groups passed independent
kernel checking, covering the seven evaluator modes and additional public
UF/LIA tactics. The full repository regression and expanded 290-target
assumption audit also passed. Wider arithmetic regression is required before
promoting the experimental path to the default.
