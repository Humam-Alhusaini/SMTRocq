# SMTRocq builds on SMTCoq

SMTCoq supplies the Rocq theory semantics, reflective Boolean/EUF/LIA checkers,
reification infrastructure, and preprocessing. SMTRocq's additions connect CVC5
to that foundation and produce compact certificates for the actual Rocq goal.
Original attribution and the CeCILL-C license remain intact. Keeping the
`SMTCoq.*` logical namespace avoids an unrelated rewrite of inherited proofs.

The native CVC5 reader and certificate producers are untrusted. A successful
solver response is not a proof: all submitted model tables, roots, clauses,
scopes, cache entries, and semantic evidence must pass verified checks and the
resulting theorem must pass Rocq's kernel. No check is disabled by this split.

`From SMTCoq Require Import SMTRocq.` is the explicit project entry point.
`From SMTCoq Require Import SMTCoq.` remains a compatibility re-export, including
the existing CVC5 tactics. The inherited tactic definitions also remain directly
available in `SMTCoq.tactics.Tactics`.
Their CVC5-specific declarations live in `theories/tactics/Cvc5.v`, separate
from SMTCoq's legacy tactic definitions.

## Standalone checker boundary

The Eunoia/CPC interpreter, signature compiler, generated rules, correctness
proofs, experiments, and solver-free benchmarks belong to
[rocq-eunoia-checker](https://github.com/Humam-Alhusaini/rocq-eunoia-checker).
They are no longer copied into SMTRocq's tracked source directories.

`external/rocq-eunoia-checker` is a Git submodule pinned by commit, not a floating
branch dependency. The small Dune adapter in
`theories/dependencies/rocq-eunoia-checker` builds its unchanged proof modules
against SMTRocq's inherited SMTCoq theories. The standalone repository also
bundles its minimal SMTCoq proof dependencies for independent builds; the
consumer does not build those duplicate copies. No second prover process or
runtime service is introduced by the dependency boundary.

The existing Rocq module names and proof bodies are preserved. Moving source
ownership does not change the checker, certificate language, or trust boundary.
Native translation metadata is generated from the pinned checker's signature
inventory. Benchmark integrity fingerprints include that dependency's sources.

## Two checking contracts

`smtrocq` proves the actual Rocq theorem from its actual hypotheses with verified
SMTCoq semantic certificates. It may compress or replace a solver derivation;
it does not claim that every CPC source instruction was validated.

`cvc5_eunoia` additionally validates the signature-generated CPC derivation and
its exact source bindings through the external checker. Unsupported rules and
resource limits still reject. Keeping the checker separately maintained does
not imply that the CVC5 backend can dispense with its verified proof dependency.
