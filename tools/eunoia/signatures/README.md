# Pinned executable subset

`Initial.eo` and `Constructors.eo` are S-expression-preserving extracts from
the cvc5 1.4.2 release signature, with comments/whitespace removed. They contain
the thirteen selected rules, `$mk_symm`, and their four constructors. They are
signature input, not a hand-written Rocq implementation of those rules.

Original root:
`cvc5-cvc5-1.4.2/proofs/eo/cpc/Cpc.eo`, SHA-256
`d13767eb873649c9f40482c99242c42081cf25308962f11c1981ce8e878770ad`.
The installed release source is an extracted archive, not a Git checkout.
`../cpc-manifest.json` records the SHA-256 of **all** files read when compiling
the original full include graph, the selected helpers/constructors, and all
596 excluded rules. Compiling either the full signature or this extract with
the same rule selection produces byte-identical `CpcGenerated.v`.

Original locations: `rules/Builtin.eo` (`ite_eq`), `rules/Uf.eo` (`refl`,
`symm`, `$mk_symm`, true/false introduction/elimination), `rules/Booleans.eo`
(`contra`, `eq_resolve`, `modus_ponens`, `not_not_elim`), `rules/Rewrites.eo`
(`eq-refl`, `eq-symm`), and `theories/Builtin.eo` (constructors).

Upstream cvc5 source is distributed under its BSD 3-clause license; the
copyright/license notice is retained in `COPYING.cvc5`.
