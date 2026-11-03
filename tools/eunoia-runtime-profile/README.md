# Generated runtime diagnostic

`profile.py` measures the existing Rocq fixture replays, without invoking a
solver or changing their inputs. Run from any directory through Python 3;
Rocq always uses the private `smtrocq-env` wrapper. No dependencies are installed.

```sh
git show c79eeba:theories/checker/eunoia/EoRuntime.v > /tmp/EoRuntime-before-sharing.v
PYTHONDONTWRITEBYTECODE=1 python3 tools/eunoia-runtime-profile/profile.py \
  --runtime /tmp/EoRuntime-before-sharing.v \
  --output /tmp/runtime-before --repeats 10 --rounds 3
PYTHONDONTWRITEBYTECODE=1 python3 tools/eunoia-runtime-profile/profile.py \
  --output /tmp/runtime-after --repeats 10 --rounds 3 \
  --refinement tools/eunoia-runtime-profile/SurfaceOutRefinement.v
EUNOIA_KEEP_TEST_DIR=1 tools/eunoia/check-generated.sh
```

Each output must be a **new directory outside the checkout**. Everything
needed to inspect a run stays there: copied `.v` files and compiled objects,
raw compiler/kernel logs, full commands with exit codes, source hashes, fixture
counts and timings in `summary.json`. Failures/timeouts mark the summary failed
and exit nonzero. `--fixture uf1 --fixture lia1` selects a diagnostic subset;
the default includes all 29 original/reduced fixtures (994 steps and 37 pushes).
The 37 pops are part of the 994 steps. No command is skipped.

The unchanged `replay_fixtures.py` decoder produces all data and assertions.
The unchanged `TraceReplay.v` and `LiaTraceReplay.v` supply the original type
queries, `derive`/`derive_assuming`, 500 fuel and `default_primitive` hook. Reduced
UF captures use the LIA-capable query, as in `check-generated.sh`. Nothing is
pretyped, precomputed or cached across changing contexts.

Each fixture has separate Rocq `Time` measurements:

* `repeated_vm`: repeat full `eval vm_compute` and compare each actual result
  with `Some (Symbol "false")`, without changing the proof goal;
* `proof_vm`: ordinary proof-producing `vm_compute` on the original equation;
* `reflexivity`: close the reduced goal;
* `qed`: kernel checking at `Qed`.

`repeated_vm` includes Ltac invocation/result-comparison overhead and warm VM
code. It is neither cold-start latency nor a pure instruction-level profile.
Rocq prints times to millisecond precision; sum measurements across fixtures
before dividing by repeats. The complete replay is recomputed each repetition;
only immutable VM bytecode is shared. Odd rounds reverse fixture order.
Every exported fixture example prints its assumptions on every round, and the
first round is also checked independently with recursive `rocq check`. Later
rounds have the same examples, so only their `Qed` checking is repeated.

`SurfaceOutRefinement.v` retains the previous surface conversion function and
proves pointwise equality with the optimized runtime for **all** nil queries,
type queries, fuel, operator lists and terms. The proof requires neither a
well-typed input hypothesis nor function extensionality. `--refinement` compiles
it, requires both `Print Assumptions` outputs to be closed, then runs independent
recursive kernel checking.

These replays test generated computation, **not the external semantic gate**.
Production still needs generated evaluation and the existing verified semantic
gate on every main step. This tool does not measure witness search, marshaling,
solver time, or whole public-tactic latency. See
[`runtime-performance.md`](../../docs/eunoia/runtime-performance.md) for results
and limits. No shared Dune/test registration is changed; run these commands
explicitly when reviewing this optimization.
