# Pinned cvc5 CPC sources

The 35 `.eo` files here are byte-identical copies of the complete recursive
include closure of cvc5 **1.4.2**, commit
`282d5e0c84baf49c780704c532f87ba66d8b513d`, `proofs/eo/cpc/Cpc.eo`.
`tools/eunoia/cpc-manifest.json` records every path and SHA256, selected/excluded
rules, helper programs, expanded definitions, primitive dependencies and generated
output hash. No source rule or arithmetic relation table was rewritten.

`Cpc.eo` SHA256:
`d13767eb873649c9f40482c99242c42081cf25308962f11c1981ce8e878770ad`.
The source closure declares 609 distinct rules, including the unsupported
`:sorry` rule `trust`. Only the explicit subset in `../../rules.txt` is emitted;
an excluded rule cannot execute.

Copied read-only from the private matching cvc5 source installation at
`/home/charles/code/friends/.toolchains/cvc5-1.4.2/cvc5-cvc5-1.4.2/proofs/eo/cpc/`.
The upstream copyright/license is retained in `COPYING`.
