# Install SMTRocq

SMTRocq is a development fork built on SMTCoq. The opam package name
`rocq-smtcoq` and the Rocq namespace `SMTCoq` are retained for compatibility;
installing the released upstream opam package alone does not install this fork.

Use Linux/POSIX, OCaml 4.14.2 or later, Rocq 9.2 with its matching standard
library, Dune 3.21 or later, Python 3, and Trakt. The pinned CI image in
[.github/Dockerfile.eunoia](.github/Dockerfile.eunoia) provides the tested toolchain.

```sh
git clone --recurse-submodules https://github.com/Humam-Alhusaini/SMTRocq.git
cd SMTRocq
opam install . --deps-only
python3 -B scripts/eunoia/install_toolchain.py
dune build -j2 @install
```

For an existing clone:

```sh
git submodule update --init --recursive
```

The submodule pins the standalone checker to a reviewed commit. Do not use
`git submodule update --remote` for a reproducible build. GitHub source archives
do not contain submodule contents; use a recursive Git checkout for development.

The private CVC5 installer verifies its pinned binary and complete signature
archive. [Solver setup](scripts/eunoia/README.md) documents the cache and flags.
The `smtrocq` tactic does not require veriT, CVC4, or ZChaff. Those solvers are
needed only for their inherited tactics and the corresponding legacy regression
suites; their original setup instructions are retained in
[the upstream installation guide](docs/upstream/INSTALL.md#installation-of-the-provers).

```coq
From SMTCoq Require Import SMTRocq.
```

See [development and validation](docs/development.md) for tests. Checker-only
builds and benchmarks belong in the separate
[Rocq Eunoia Checker repository](https://github.com/Humam-Alhusaini/rocq-eunoia-checker).
