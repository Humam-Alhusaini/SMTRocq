# Focused proof-construction performance investigation

This child investigates the public tactic's marshaling and VM helper boundary
at parent `5523d5ed65fa6fa34a1bbd7ca7a64b8f0588d4ca`, including `3dd364d`
(unchanged closed default fuel) and `53e2c32` (actual goal sigma). It does not
establish overall port completion, LIA acceptance, or competitive performance.
The working branch is `t3/profile-proof-construction` in
`/home/charles/.t3/worktrees/SMTRocq/t3-100d9c16`.
The production helper change is local commit
`5b45f67e47d981c6298017e4f3de7bdd96b44387`; the tooling/report commit follows it.

## Scope and retained checks

The production change only hoists `Ascii`, `String`, and `EmptyString`
constructor lookups inside individual `string`/`decode_string` calls in
`src/eunoia_backend/eunoiaRocq.ml`. Each call still resolves names in the current
environment. There is no persistent cache, semantic-result memoization, new
resource limit, or new assumption. Character bit order, constructor applications,
decoding validation and failure branches are preserved. The signature inventory
is still computed from the loaded generated constant on every invocation.

The backend, witness search, adapter, generator, theories, live suites, shared
Dune/plugin/tactic files, and benchmark harness are unchanged. Every original
CPC step retains generated evaluation, exact source/root/premise/result binding,
the local semantic gate, the concrete goal theorem, `exact_check`, and `Qed`.
Temporary `NewProfile` probes wrap the original helper operations and are
removed from production. The new isolated tools require no integration stanza.

## Reproduction and evidence

All Rocq/OCaml/Dune commands use
`/home/charles/code/friends/.toolchains/smtrocq-env` (Rocq 9.3.0, OCaml 4.14.2).
No dependencies were installed, no reference checkout was used, and no solver
options were changed. Live goals use the backend's pinned cvc5 1.4.2 executable.
The arithmetic case uses existing `backend_lia_replay`, including production
Micromega witnesses; it is not a live LIA solver benchmark.

The exact argument arrays, working directories, exit codes and outputs are in
each artifact directory's `command.json` and `output.log`. Generated sources,
`.vo` files, numeric native profiler traces and assumption audits are retained.

```sh
# Cold build: exit 0; /tmp/smtrocq-profile-base-build.log
/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2 @install

# Unmodified baseline: exit 0; all four Qed, audits and recursive checks pass.
python3 -B tools/eunoia-profile/run.py \
  --output /tmp/smtrocq-proof-profile-native-fixed --kernel-check

# Baseline helper probes: exit 0; all Qed, audits and rejection controls pass.
python3 -B tools/eunoia-profile/instrument.py install \
  --backup /tmp/smtrocq-proof-profile-instrument-backup
/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2 \
  src/eunoia_backend/eunoia_backend.cmxs
python3 -B tools/eunoia-profile/run.py \
  --output /tmp/smtrocq-proof-profile-instrumented --controls
python3 -B tools/eunoia-profile/instrument.py restore \
  --backup /tmp/smtrocq-proof-profile-instrument-backup

# After the local constructor hoist; separate native and helper measurements.
/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2 \
  src/eunoia_backend/eunoia_backend.cmxs
python3 -B tools/eunoia-profile/run.py \
  --output /tmp/smtrocq-proof-profile-hoist-native --kernel-check --controls
python3 -B tools/eunoia-profile/instrument.py install \
  --backup /tmp/smtrocq-proof-profile-hoist-backup
python3 -B tools/eunoia-profile/run.py \
  --output /tmp/smtrocq-proof-profile-hoist-instrumented
python3 -B tools/eunoia-profile/instrument.py restore \
  --backup /tmp/smtrocq-proof-profile-hoist-backup
/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2 \
  src/eunoia_backend/eunoia_backend.cmxs
```

All four goals are fixed in `tools/eunoia-profile/run.py`: abstract reflexivity,
abstract unary congruence, positive predicate transport, and integer `x+0=x`
source replay. They preserve quantified carriers inside the theorem and use
the actual goal sigma. Each case starts a fresh compiler. `Time tactic` covers
preprocessing, export, solver interaction (live UF only), candidate construction
and checked tactic application. Imports and `Time Qed` are separate. Process
times include startup and profiling output and are not tactic times.

An initial driver attempt failed after successfully compiling reflexivity
because Rocq appended `.json` to a supplied `.json` profile basename. That
failed invocation is retained at `/tmp/smtrocq-proof-profile-native`; the
corrected driver supplies an extension-free basename. An initial attempted
helper build targeted consumer plugins only; it did not rebuild the changed
dependency implementation. `/tmp/smtrocq-proof-profile-helpers` therefore has
no helper events and is not used as helper evidence. The final driver builds
the measured library itself and records its binary hash. The redundant
consumer-only build started during the cold build was interrupted (exit 130);
it supplies no validation result. These are distinct from successful runs.

## Native timings and limits

The baseline uses production source SHA256
`d4c5f8a4759950113bae76cfa373ee4e0542911b9737e64680bd1a3a76a9f53e`;
the hoist uses
`9647220f930d12c21d21254f11f304bdb34335d550c25b2fe726b8b3572f03fe`.
Only the two string helpers differ. Each timing is one sequential probe, using
the same statement, compiler settings, default fuel and native profiling
components. These are observations, not a latency improvement claim.

| Case | Before tactic / Qed (s) | Hoist tactic / Qed (s) |
| --- | --- | --- |
| Abstract reflexivity | 0.346 / 0.027 | 0.374 / 0.026 |
| Abstract congruence | 3.637 / 1.070 | 3.970 / 0.996 |
| Predicate transport | 2.430 / 0.491 | 2.501 / 0.477 |
| Arithmetic source replay | 0.184 / 0.020 | 0.470 / 0.020 |

Complete rows are in the native runs' `results.json` files. In particular, the
arithmetic timing increase is reported, not suppressed. This tiny local change
does not establish an end-to-end speedup under these uncontrolled conditions.
Jobs elsewhere on this machine were concurrent: baseline starting load averages
were `[5.119, 5.633, 6.248]`, baseline helper probes `[6.071, 6.084, 6.331]`,
and the hoist's native run `[5.501, 5.957, 6.278]`. CPU affinity and OS caches
were not controlled. No comparison with veriT, Logos, Ethos, Lean-SMT, or
Sledgehammer follows from these probes.

## Measured boundaries

The baseline helper run's congruence trace records:

| Boundary | Calls | Inclusive seconds |
| --- | ---: | ---: |
| Global name resolution | 14,043 | 0.056220 |
| String marshaling | 446 | 0.016993 |
| Term marshaling | 59 | 0.019727 |
| Computed-term decoding | 17 | 0.006604 |
| Generated signature inventory normalization | 1 | 0.108126 |
| Source-root clause encoding | 4 | 0.029714 |
| Generated candidate derivation normalization | 13 | 0.146738 |
| Final checked Boolean conversion | 1 | 1.138369 |
| VM compilation, across these stages | 20 | 0.003356 |

These are **overlapping** spans with instrumentation overhead. For example,
global resolution is also inside string marshaling/decoding, and VM compilation
is inside VM normalization/conversion. They must not be added or interpreted
as disjoint percentages. The 13 candidate derivations do not replace the
generated evaluations performed again by the final reflective checker.

The hoist's helper probe reduces congruence global lookups from 14,043 to 4,095
(9,948 fewer lookups on the same theorem), with the same 13 candidate generated
derivations, four clause encodings, and one final checked conversion. Measured
global-resolution spans are 0.056220 / 0.016337 s before/after; string marshaling
0.016993 / 0.007975 s, and decoding 0.006604 / 0.004454 s. These instrumented
figures include probe overhead and do not establish the uninstrumented saving.
The verified improvement claimed here is fewer repeated constructor lookups;
the native timing table establishes no overall latency improvement.

| Probe | Global lookups before / after | Generated candidate calls before / after |
| --- | ---: | ---: |
| Reflexivity | 9,709 / 1,795 | 5 / 5 |
| Congruence | 14,043 / 4,095 | 13 / 13 |
| Predicate | 13,444 / 3,788 | 13 / 13 |
| Arithmetic replay | 8,852 / 1,364 | 2 / 2 |

Every row also retains one explicit final checked conversion, followed by
checked theorem application and `Qed`. This does not count the evaluations
performed inside that final conversion or subsequent typechecking.

The native baseline's congruence `Qed` trace separately records one VM
conversion taking 1.042967 s, compared with about 1.134 s in the tactic's initial
checker conversion; VM compilation is only milliseconds. Its native formatted
subtimes also identify ordinary conversion/unification during checked tactic
application. Those categories overlap. Numeric trace timestamps, rather than
adding formatted subtimes, should be used for further allocation of that time.
The installed profiler's formatting can round a seconds component separately
from its millisecond remainder; its text subtimes are not exact decimal seconds.

## Safe follow-up outside this child's ownership

Large UF latency is in actual checker execution and repeated checked conversion,
not VM compilation. `Typing.judge_of_cast` in the private Rocq runtime calls
`check_actual_type`/ordinary unification even for a VM cast; kernel
`Typeops.check_cast` dispatches VM casts to VM conversion. The public backend's
`Tactics.exact_check` and later `Qed` both remain mandatory. Replacing them with
unchecked entry points, hiding the cast behind an assumption, or reusing a
semantic success from an earlier environment is not an optimization option.

At the measured parent, a candidate follow-up was factoring immutable
`tables_wf` guards out of `EunoiaAdapter.eval_with`'s changing payload/premise
arguments, following the existing local/scoped callback sharing change. Any
such refactor needs a kernel-checked refinement and the same rejection tests;
every step must still run generated derivation and exact bindings/gate. Another
candidate is reducing repeated syntactic allocation inside the verified
generated interpreter, with exact term equality and configuration/input-scoped
identity; this profile does not establish that a particular cache is useful.
The coordinator subsequently reports that `c79eeba` already includes source
guard sharing in `typeof`/`eval_with`, live LIA `46cecc0` via `72bbd45`, and
generated `arith-geq-tighten` `159d204` (49 rules, 53 helpers). That newer parent
was deliberately not merged into this controlled pair. The integrated parent
must be reprofiled before attributing its latency to these older measurements
or proposing the already-integrated guard refactor again.

The coordinator reports that LIA branch `46cecc0` adds 15 checked public goals,
while some disjunctive/inconsistent goals still time out after 300 s. That
branch and witness scheduling performance are separate work and were not
integrated or benchmarked here. This small source arithmetic replay cannot
explain those long-running witness searches.

## Verification and incomplete work

The before/after native commands above exited 0. All four positives closed with
`Qed`, printed the existing 52 baseline assumptions and introduced none.
Both native runs passed recursive independent `rocq check` for all four proof
modules with VM enabled and no admitted dependencies. The post-change control
module also passed recursive kernel checking. False controls have no
assumptions; source/local control lemmas have the same 52 baseline assumptions.
Temporary baseline and post-change helper runs exited 0 and passed all four
positive assumption audits. Both source restorations exited 0 and the final
production file matches the hoist SHA256 above, without profiling hooks.

`Controls.v` checks false integer equality and arbitrary-function injectivity,
changed arithmetic coefficient/premise/conclusion/root, an invalid local gate,
and an invalid supported unused step. Existing test-plugin mutations are used;
no acceptance path is replaced. Each enclosing positive lemma closes with
`Qed`, prints assumptions, and passes the baseline comparison.

```sh
# Exit 0; six tooling tests, log /tmp/smtrocq-proof-profile-tool-tests.log.
python3 -B -m unittest discover -s tools/eunoia-profile -p test_profile.py -v

# Final production plugin and existing checked integration replays.
# Exit 0; /tmp/smtrocq-proof-profile-final-replays-build.log.
/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2 \
  src/eunoia_backend/eunoia_backend.cmxs \
  src/eunoia_backend/tests/integration/Proof.vo \
  src/eunoia_backend/tests/integration/Public.vo \
  src/eunoia_backend/tests/integration/Lia.vo
```

The combined successful probe/audit/kernel validation is recorded at
`/tmp/smtrocq-proof-profile-validation.json`: 16 checked positive probes across
the four focused runs, nine recursive native kernel checks, and both control
audits. Production `Proof.vo`, `Public.vo`, and `Lia.vo` were rebuilt successfully
after restoration. `git diff --check` exited 0. No shared Dune integration is
required for the standalone developer scripts.

The full acceptance suites, full regression after the newer parent merge,
long-running live LIA witness cases, representative benchmarks, and integrated
parent reprofiling remain coordinator/other-owner work. This child does not
claim them complete. No soundness lemma was added; all new probe/control proof
declarations nevertheless print assumptions and undergo the audits above.
