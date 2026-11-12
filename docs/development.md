# Develop SMTRocq

Initialize the pinned checker before building:

```sh
git submodule update --init --recursive
python3 -B scripts/eunoia/install_toolchain.py
```

Production tactic validation, including strict and compiled certificate paths:

```sh
sh scripts/eunoia/ci.sh
```

The workflow builds the Rocq theories and public tactic suites, runs the native
proof-reader/producer tests and corruption controls, replays fresh public proofs,
audits assumptions, and independently rechecks proofs with Rocq's kernel.
`docs/checker-assumptions.txt` records SMTCoq's inherited assumption baseline;
this cleanup introduces no new axiom or admitted proof.

The repository-wide `dune build -j2 @install @runtest` also includes legacy
veriT/CVC4/ZChaff tests and requires those binaries. Tactic benchmarks are
[documented separately](../benchmarks/eunoia/README.md). Do not run CPU-heavy
builds or audits concurrently with comparative timing runs.

## Where to make a change

Change the CVC5 interface, native certificate production, public tactics, and
end-to-end tactic benchmarks here. Preserve SMTCoq attribution when changing
inherited theories or infrastructure.

Change Eunoia signatures, generated CPC checking, checker proofs, interpreter
experiments, or solver-free checker benchmarks in
[rocq-eunoia-checker](https://github.com/Humam-Alhusaini/rocq-eunoia-checker).
Validate that repository independently, then update the submodule commit in a
separate reviewed SMTRocq change and rerun tactic validation. Do not restore
local copies of the checker sources or edit its build-directory copies.

The archived pre-split development notes remain available in Git history and
the standalone checker repository. Only the dated production tactic benchmark
report is retained here; its measurements apply to its recorded checkpoint.

CI belongs to this fork: the pinned SMTRocq workflow checks its own code and
initializes the checker dependency. Upstream-only Sniper update and downstream
Nix matrix workflows are not inherited by this repository.
