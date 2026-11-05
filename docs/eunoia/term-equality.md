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
