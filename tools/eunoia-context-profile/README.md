# Explicit checked-context experiment

This driver reuses the existing native Rocq profile runner on five **live public
`tactic` goals**, including coefficient normalization and scoped LIA. It changes
no solver, fuel, source, capacity or witness settings. Build first:

```sh
/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2 @install
ROCQ_PROFILE_COMPONENTS=-unification python3 -B tools/eunoia-context-profile/run.py \
  --output /tmp/context-baseline --repeat 2 --timeout 180 --controls
python3 -B tools/eunoia-context-profile/summarize.py /tmp/context-baseline \
  > /tmp/context-baseline/timings.json
```

Every successful row requires a fresh `.vo`, `Qed`, a checked marker and a
baseline assumption audit. The runner retains raw native profiles, commands,
compiler logs, source/artifact hashes, source diffs and load averages. Its
`context-metadata.json` additionally fingerprints all eight context/runtime
modules before and after the run and fails if they changed. `--kernel-check`
requests recursive independent kernel checks per profile theorem; a single
combined recursive check is cheaper for the complete validation suite.

`summarize.py` extracts raw wall/user/system times separately for tactic and
`Qed`, plus final `vm_conv` and process wall time. Inclusive profile events
**overlap** and must not be added. Shared-machine timing variation is not a
competitive performance result. See
[the experiment report](../../docs/eunoia/checked-context-performance.md) for
actual pins, results, proof and control coverage, commands, and limitations.

For exact-input, same-process conversion pairs, with the trial patch applied:

```sh
ROCQ_PROFILE_COMPONENTS=-unification python3 -B tools/eunoia-context-profile/paired.py \
  --profiles /tmp/context-candidate --output /tmp/context-paired --repeat 3
```

This requires the accepted `Case.vo` files produced by the public-goal driver.
It prints each full proof, extracts its actual `checker`/`checker_b` expression,
hashes that expression, and alternates guarded/context order using identical
arguments. Each measured lemma reruns the entire checker, proves `= true`,
closes with `Qed` and prints assumptions; the qualified auditor checks every
lemma. Raw triples in `results.json` are `[wall, user CPU, system CPU]`, with
alternating compute/Qed entries in `order`. The compiler process includes all
six lemmas for one workload, so its process wall time is not a per-call value.
The printed original proof, exact expression, generated source and profiles
are retained for inspection. Supported entry points are deliberately explicit;
unknown entry points or truncated printing fail rather than dropping a case.
