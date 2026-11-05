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
