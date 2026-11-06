# Eunoia runtime computation profile

This child task measures generated computation, independently of the existing
SMTCoq semantic certificate gate. It does not establish overall port completion
or an end-to-end tactic speedup. The coordinator owns integration and full
regression after combining the other performance work.

## Scope and reproducibility

Base: `c79eeba` on `smtrocq/cvc5-eunoia`. Child branch:
`t3/profile-eunoia-runtime`. Only `theories/checker/eunoia/EoRuntime.v`,
`tools/eunoia-runtime-profile/` and this report are owned by this task.
No generator, generated signature, arithmetic/order code, semantic adapter,
core/gate, backend, witness producer, benchmark harness or shared Dune/tactic
file is changed. No push, PR, dependency installation or external comment was
performed. Neither Logos nor Ethos was used.

The profiler copies the actual runtime, syntax, arithmetic, ordering, generated
signature and existing replay modules into a fresh `/tmp` directory. It uses
the existing decoder for all actual fixture bytes and compiles standalone
modules with the private toolchain:

```sh
/home/charles/code/friends/.toolchains/smtrocq-env rocq compile \
  -q -Q . SMTCoq.checker.eunoia MODULE.v
/home/charles/code/friends/.toolchains/smtrocq-env rocq check \
  -silent -Q . SMTCoq.checker.eunoia SMTCoq.checker.eunoia.MODULE
```

Rocq is 9.3.0, compiled with OCaml 4.14.2. Both variants use the same compiler
flags, `derive`/`derive_assuming`, default primitive hook, structural type
queries and **500 replay fuel**. The public backend's default 10000 fuel is not
changed; this diagnostic measures the existing fixture replays. The refinement
theorem quantifies over every fuel value.

The workloads contain seven original UF captures (98 steps), eight original
LIA captures (411 steps, including strict-shift tightening), and fourteen
reduced UF/LIA captures (485 steps). **All 994 steps, including 37 pops, run**;
37 pushes are retained separately. The reduced UF captures retain the
LIA-capable query used by the original regression harness. Every main step's
generated evaluation and external semantic gate remain required in production.

`Time do N (let result := eval vm_compute in (...) in constr_eq ...)` measures
repeated complete computation and checks every result against the expected
`false` conclusion. It does not close or change the proof goal. The subsequent
ordinary `vm_compute`, `reflexivity` and `Qed` are timed separately. Every fixture
example prints its assumptions, and the first complete round additionally
passes recursive independent kernel checking. Later rounds reverse fixture
order alternately. Repetition shares VM code, not changing proof contexts or
precomputed fixture results.

## Generic sharing candidate

The previous `surface_out_with` converts the first argument of an application
at fuel `k` to supply the nil/type query, then converts it again at the same
fuel while visiting the argument list for a non-list application. Nested
ordinary applications repeatedly duplicate this work. Type queries during
rule checking also use this conversion, so the cost recurs within one step.
This is a concrete source-level duplication; linear named lookup and structural
comparison were hypotheses, not independently established hotspots.

The candidate shares that first conversion **within one call**, rebuilding an
ordinary application from its already converted head argument plus converted
tail. Nil-terminated applications retain their original list traversal. Failed
first conversion still fails; known operators with unavailable nils still fail.
No context cache, global memoization, prepared type information, name dispatch,
resource-bound adjustment or missing-primitive fallback is introduced.

`tools/eunoia-runtime-profile/SurfaceOutRefinement.v` retains the exact old
conversion body and proves `surface_out_with_refinement` pointwise for arbitrary
nil queries, type queries, operator lists (including duplicates), terms and
fuel. `visit_terms_pointwise` is its elementary list traversal lemma. Neither
requires function extensionality, a well-typedness premise or any new axiom.
Both print **Closed under the global context**. Evaluator diagnostics, ordered
helper matching, lazy conditionals, guards, binder checks, type outputs and
primitive hooks are unchanged.

## Measurement and validation artifacts

Both repeated runs exited **0**: three rounds of ten evaluations of each
fixture, with alternate forward/reverse fixture order. Comparison exited **0**
and verifies identical timing source files, fixtures, compiler versions and
non-runtime module hashes. CPU time below is user plus system time, normalized
per complete cohort pass, then median across rounds. Cohort medians need not
sum to the median of the complete pass.

| Fixtures | Phase | Before CPU s | After CPU s | After / before |
| --- | --- | ---: | ---: | ---: |
| Original UF | repeated_vm | 0.3359 | 0.2619 | 0.780 |
| Original UF | proof_vm | 0.3160 | 0.2340 | 0.741 |
| Original UF | qed | 0.3280 | 0.2480 | 0.756 |
| Original LIA | repeated_vm | 2.0157 | 1.3105 | 0.650 |
| Original LIA | proof_vm | 1.9550 | 1.2820 | 0.656 |
| Original LIA | qed | 1.9780 | 1.2790 | 0.647 |
| Reduced UF/LIA | repeated_vm | 2.5665 | 1.6546 | 0.645 |
| Reduced UF/LIA | proof_vm | 2.5280 | 1.6070 | 0.636 |
| Reduced UF/LIA | qed | 2.5420 | 1.6570 | 0.652 |
| All fixtures | repeated_vm | 4.9048 | 3.2115 | 0.655 |
| All fixtures | proof_vm | 4.7990 | 3.1240 | 0.651 |
| All fixtures | qed | 4.8470 | 3.1860 | 0.657 |

The full-pass repeated evaluation range was
**4.7404–5.0021 CPU s before**, versus
**2.9954–3.2702 CPU s after**. The median reduction is
**34.5%** in this computation diagnostic. The separate `proof_vm` and `Qed`
measurements show a similar local reduction. This supports retaining the generic
sharing change; it is not a whole-tactic performance claim.

Exact measurement commands, run from the child checkout:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 tools/eunoia-runtime-profile/profile.py \
  --output /tmp/smtrocq-runtime-before-r1 --repeats 10 --rounds 3
PYTHONDONTWRITEBYTECODE=1 python3 tools/eunoia-runtime-profile/profile.py \
  --runtime /tmp/smtrocq-runtime-sharing.v \
  --output /tmp/smtrocq-runtime-after-r1 --repeats 10 --rounds 3 \
  --refinement tools/eunoia-runtime-profile/SurfaceOutRefinement.v
PYTHONDONTWRITEBYTECODE=1 python3 tools/eunoia-runtime-profile/compare.py \
  /tmp/smtrocq-runtime-before-r1 /tmp/smtrocq-runtime-after-r1 \
  --output /tmp/smtrocq-runtime-comparison
```

The before run was made before applying the runtime edit. The after run used a
temporary candidate whose bytes now exactly match the committed runtime.
The hashes are:

* Old runtime: `2d4d8d6c8f529234117981e9e28d6cdd44d68c4864f47198fc9a4a1c188693fe`.
* Shared runtime: `ad77b97b9717c1b6f9add760c3f338389bdc419ee815725ed4d575e3bd8fa4d4`.
* Unchanged generated signature: `a9b6ee0e0c98df2e86b5f10a3327f780698a85161f94d4108dab879add0ae6e5`.

Raw artifacts remain outside Git:

* `/tmp/smtrocq-runtime-before-r1/summary.json` and `Profile{0,1,2}.log`.
* `/tmp/smtrocq-runtime-after-r1/summary.json` and `Profile{0,1,2}.log`.
* Both directories contain `Profile0-kernel.log` and all copied/compiled modules.
* The after directory also contains `SurfaceOutRefinement.{v,vo,log}` and
  `SurfaceOutRefinement-kernel.log`: both new lemmas are closed, and the recursive
  independent check exited 0.
* `/tmp/smtrocq-runtime-comparison/comparison.{json,md,html}` contains per-round
  numerical data, the table and chart.

The JSON summaries record every subprocess command, exit code, source hash,
fixture hash/count and timing, alongside the generated `.v`, `.vo` and raw logs.
The README supplies repeatable baseline extraction and after-run commands for
the final source tree. No solver was run during these computation profiles.

Final standalone validation:

```sh
EUNOIA_KEEP_TEST_DIR=1 tools/eunoia/check-generated.sh \
  > /tmp/smtrocq-runtime-after-check-generated.log 2>&1
```

Exit **0**. All 42 Python tests passed, regenerated code and manifest matched
byte-for-byte, all 994 original/reduced steps computed, and the runtime, helper,
source/guard mutations, strict-tightening mutations, lazy branches, missing
natives, failed matched cases and other fail-closed examples compiled. The
script's recursive independent kernel checks passed. Retained source/compiled
artifacts are in `/tmp/smtrocq-eunoia.9n0JgEQz/`. The corresponding unchanged
baseline command also exited 0, with log
`/tmp/smtrocq-runtime-baseline-check-generated.log` and retained directory
`/tmp/smtrocq-eunoia.BtYiDsfw/`.

The new refinement proof's two `Print Assumptions` statements both report
**Closed under the global context** in
`/tmp/smtrocq-runtime-after-r1/SurfaceOutRefinement.log`. All 29 fixture examples
per round also report closed assumptions. No new semantic soundness theorem or
assumption is introduced.

Public-tactic compatibility checks:

```sh
/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2 \
  @install unit-tests/eunoia_tactics.vo \
  > /tmp/smtrocq-runtime-live-smoke.log 2>&1
python3 tools/audit-eunoia-assumptions.py \
  --import SMTCoq.tests.eunoia_tactics \
  --theorem eunoia_live_reflexivity \
  --theorem eunoia_live_congruence \
  --theorem eunoia_quantified_carrier \
  --loadpath _build/default/unit-tests SMTCoq.tests \
  --output-dir /tmp/smtrocq-runtime-live-smoke-assumptions
```

Both commands exited **0**. The existing smoke file closes integer reflexivity,
integer function congruence and fully quantified abstract-carrier congruence
with the actual public tactic, and preserves both false-goal rejection controls.
The audit reports `passed: true` and empty `new_assumptions` for all three
exports. Its complete commands and assumption sets are in
`/tmp/smtrocq-runtime-live-smoke-assumptions/summary.json`. Existing Uint63 and
proof-irrelevance assumptions remain within the checked repository baseline;
they are not new assumptions introduced by this optimization. The `@install`
target also built the existing backend integration modules. This is not a full
`dune runtest` or a benchmark matrix.

Final `git diff --check` and byte comparison of the measured candidate against
the production runtime exited **0**. Shared Dune/tactic files are unchanged.

The initial profiler prototype failed with exit 1 because it placed an `idtac`
after `reflexivity` had closed the goal. It is preserved at
`/tmp/smtrocq-runtime-baseline/`. The label/parser placement was corrected;
no runtime check was changed. Preliminary one-repeat runs in
`/tmp/smtrocq-runtime-{baseline,sharing}-pilot/` both passed, but overlapped
other validation and are not the repeated measurement evidence.

## Remaining limits

This is a local, warm-VM computation experiment, with millisecond-resolution
Rocq timing and Ltac result-comparison overhead. Other jobs may use the same
machine. The beginning of the repeated baseline also overlapped the tail of
baseline regression validation; subsequent timing rounds and the candidate run
were sequential locally. Source/build isolation does not mean exclusive CPU
access. Per-round CPU ranges are retained rather than claiming dedicated-machine
latencies. Whole compiler process wall time also includes parsing, typechecking,
VM compilation, `Qed`, module saving and startup; recursive `rocq check` includes
library dependencies. These are distinct from repeated evaluation time.

The measurements do not isolate every runtime function, measure live search or
marshaling, or demonstrate a public-tactic/solver benchmark improvement. No
full benchmark matrix is run. The coordinator still needs composed regression
and any end-to-end performance comparison with the backend/witness changes.
The optional standalone refinement/profiling commands require explicit execution;
no shared Dune registration is requested or modified by this child.
