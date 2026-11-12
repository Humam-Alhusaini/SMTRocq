# Focused proof-construction probes

Run from an idle, isolated checkout. This is a four-goal developer probe, not
the acceptance suite or a backend benchmark matrix. It imports the existing
integration-test plugin for its explicitly labeled arithmetic replay and
mutation controls. It needs no shared Dune changes or additional dependencies.

```sh
/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2 @install
python3 -B -m unittest discover -s tools/eunoia-profile -p test_profile.py -v
python3 -B tools/eunoia-profile/run.py \
  --output /tmp/eunoia-profile-native --kernel-check --controls
```

The driver first builds the measured library's own `.cmxs`, because building
only a consumer plugin can leave an unchanged-interface dependency's native
implementation stale. Build time is recorded separately. Each positive starts
a fresh compiler process, runs the public `cvc5_eunoia` tactic (or the specified
source arithmetic replay), closes with `Qed`, and prints assumptions. The
existing assumption auditor compares qualified names with the baseline.
`--kernel-check` also runs recursive `rocq check -bytecode-compiler yes`, without
dependency admissions. All commands, exits, logs, source/plugin hashes, load
averages, source files, `.vo` files, and native Rocq Profile JSON traces are
retained outside Git. A rejected control is enclosed in `Fail`; the enclosing
positive lemmas still close with `Qed` and are audited.

`Time tactic` excludes imports and `Qed`. `Time Qed` is separate. Process time
includes compiler startup, imports, Dune, and profiling output. Profiles include
instrumentation overhead. Inclusive stage times overlap and must not be added.
`visible_self_s` subtracts only visible child events; Rocq suppresses some
components by default. For exact conversion spans, set
`ROCQ_PROFILE_COMPONENTS=-unification` on **both** compared commands. Read numeric
timestamps in the JSON, rather than interpreting Rocq's formatted subtimes as
exact seconds. Profiling does not isolate solver time or witness search.

Optional temporary probes split generated VM normalization, constructor lookup,
string/term marshaling, decoding, and final checker conversion. They wrap the
existing operations; no computation or check is replaced. Installation and
restoration fail if an anchor or saved source hash has changed.

```sh
python3 -B tools/eunoia-profile/instrument.py install \
  --backup /tmp/eunoia-profile-original
python3 -B tools/eunoia-profile/run.py --output /tmp/eunoia-profile-helpers
python3 -B tools/eunoia-profile/instrument.py restore \
  --backup /tmp/eunoia-profile-original
/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2 \
  src/eunoia_backend/eunoia_backend.cmxs
git diff -- src/eunoia_backend/eunoiaRocq.ml
```

Always restore and rebuild after temporary profiling, including after a failed
run. Keep the backup until restoration is verified; do not commit temporary
probes. Never interpret a run without the `Eunoia.*` events as a helper profile.
The timeout covers a compiler process and its process group; the production
solver retains its own timeout and detached-process cleanup. This developer
driver is not a replacement for the benchmark harness's stronger descendant
timeout diagnostics.
