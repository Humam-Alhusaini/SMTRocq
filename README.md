# SMTRocq

SMTRocq builds upon [SMTCoq](https://github.com/smtcoq/smtcoq) to provide a
CVC5-backed SMT tactic for Rocq. It reuses SMTCoq's theory semantics, verified
reflective checkers, reification, and preprocessing. SMTRocq adds the CVC5 proof
interface and compiles untrusted solver proofs into compact checked certificates.

This is a development fork of SMTCoq, not the upstream SMTCoq distribution.
The inherited code, authorship, Git history, and [CeCILL-C license](LICENSE) are
preserved. See [AUTHORS](AUTHORS) for SMTCoq's original contributors. Existing
`SMTCoq.*` logical names and the `rocq-smtcoq` package name remain for compatibility.

```coq
From SMTCoq Require Import SMTRocq.
From Stdlib Require Import ZArith.
Local Open Scope Z_scope.

Goal forall x y : Z, x <= y -> y < x + 1 -> x = y.
Proof. smtrocq. Qed.
```

The current tactic supports tested uninterpreted-function and linear integer
arithmetic goals, including the supported proved facts for Rocq division and
modulo by constants. Certificates and the resulting theorem are checked in
Rocq; an UNSAT answer or native compiler result is never sufficient evidence.

The **Rocq Eunoia Checker lives in its own repository**:
[Humam-Alhusaini/rocq-eunoia-checker](https://github.com/Humam-Alhusaini/rocq-eunoia-checker).
Its generated CPC rules, interpreter, correctness proofs, standalone benchmarks,
and checker experiments are maintained there. SMTRocq consumes an exact pinned
revision through a Git submodule; checker implementation files are no longer
tracked in this repository.

| Location | Responsibility |
| --- | --- |
| `theories/structures`, `theories/utils`, `theories/checker` | Inherited SMTCoq semantics and reflective checkers |
| `src/eunoia_backend`, `src/eunoia`, `src/eunoia_witness` | SMTRocq's CVC5 interface, proof reader, and untrusted certificate producers |
| `theories/tactics/Cvc5.v`, `theories/SMTRocq.v` | SMTRocq's public tactics, layered on SMTCoq |
| `external/rocq-eunoia-checker` | Pinned dependency owned by the standalone checker repository |
| `theories/dependencies/rocq-eunoia-checker` | Build adapter; compiles unchanged dependency proofs against SMTCoq |
| `unit-tests`, `benchmarks/eunoia` | End-to-end tactic tests and measurements |

Clone with the checker dependency:

```sh
git clone --recurse-submodules https://github.com/Humam-Alhusaini/SMTRocq.git
cd SMTRocq
```

For an existing checkout, run `git submodule update --init --recursive`.
[Installation](INSTALL.md), [architecture and repository boundaries](docs/architecture.md),
[development](docs/development.md), and [tactic benchmarks](benchmarks/eunoia/README.md)
describe the current project. The [dated performance report](docs/benchmarks/smtrocq-tactic-2026-11-11.md)
retains its exact checkpoint, failures, and timing boundaries; it is not a
benchmark of this repository cleanup.

The compatibility `SMTCoq` entry point continues to export the inherited and
CVC5 tactics. Prefer `From SMTCoq Require Import SMTRocq.` to identify this
project explicitly. The optional
`cvc5_eunoia` tactic additionally validates the CPC source derivation through
the external checker; `smtrocq` certifies the actual theorem using semantic
certificates. The two contracts are documented in the architecture guide.
