# Short-circuit source-term equality

Application equality first compares the function subtree and compares the
argument subtree only if that succeeds. The preceding implementation passed
both recursive comparisons as arguments to Boolean conjunction; the VM's
argument evaluation performed both comparisons even when the first failed.

`EoSyntax.term_eqb_refinement` states equality with the original recursive
definition for every pair of source terms. Its proof is `reflexivity`: the
implementations are definitionally equal. No extensionality, additional axiom,
new source rule or change to the semantic checker is involved.

This targets failed comparisons during source matching and list operations.
A deliberately early-mismatching tree diagnostic showed avoided work, while
equal inputs had similar cost. Those concurrent synthetic measurements do not
establish a tactic speedup; a matched frozen-revision comparison is required.

## Validation and matched tactic result

The full build and repository regression passed. All **291 assumption-audit
targets** passed, including the closed refinement theorem, followed by recursive
kernel checking. Fourteen fresh UF/LIA positive/corruption groups across all
seven evaluator modes also passed independent kernel checking. The standalone
snapshot passed its build, regression, **114-target** assumption audit and fresh
UF/LIA source-smoke kernel check.

Frozen revisions `ea0fff2` and `983c85a` ran the unchanged standard workload in
old/new/new/old order, with optimized proof acceptance enabled in both, adaptive
sharing preserved and a 30-second compiler timeout. Each version/backend
proved all 36 positives and rejected all four false controls. Workload hashes
matched; checker fingerprints remained stable within each revision.

CVC5/Eunoia tactic totals were **37.739 s reference versus 35.770 s short-circuit**
(5.2% lower), with `Qed` at **2.048/2.021 s**. The veriT control also improved,
**3.031 s versus 2.899 s** (4.4%), with `Qed` at 1.207/1.193 s. These small
samples do **not** establish a clear additional tactic speedup beyond control
variation. The change is retained for its proved equivalence and avoided
unnecessary subtree traversal; synthetic mismatch gains are not presented as
tactic gains. The backend remains about 12 times slower than veriT on this
suite's tactic time.

[Exact rows and hashes](term-equality-comparison-2026-11-05.json) retain the
measurements separately from the larger proof-acceptance improvement.
