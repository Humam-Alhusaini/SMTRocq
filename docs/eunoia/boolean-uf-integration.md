# Public typed Boolean UF integration

This implementation starts at parent `4f87e02` and merges the explicitly
authorized `0f688a7bec6c0ac70c483c33cfc6885858c4d20d` and
`b59cb57c662c9e944a2dc397725d7ee891076253` dependencies. The latter includes
table tracing and its two regressions, with the original search restored.
Implementation commit: `a3a4cf5`.

## Gate and producer contract

`EunoiaLocal.command` now has the existing `Command step expected` constructor
and a local `BoolCongrCommand pos result equalities expected` constructor.
Existing positional certificate sources remain valid. The `action` projection
now returns `option Checker_Ext.step`; it returns `None` for the local command.
The backend diagnostic prints the actual computed command, including its
expected clause. It never substitutes a dummy core operation.

The core decoder and execution checks are unchanged, factored into
`execute_core`; its binding lemma is now `execute_core_binding`.
`execute_bool` checks a fresh bounded output, every explicit formula reference,
and `EunoiaBool.congr_clause`. `None` rejects. The raw clause is stored using
`S.set_clause`, then its canonical result must equal the canonical, bounded
`expected` exactly and differ from the failure clause `C._true`.
`execute_bool_binding` exposes these checks. `execute_valid`, `run_valid`, and
`gate_correct` use `EunoiaBool.congr_clause_sound` and `S.valid_set_clause`.
The gate retains its authoritative `Atom.wt` premise and table checks.

The new operation reads no clause slots and asserts no equality premise.
The clause is conditional on every supplied equality. Existing binary checked
resolution must discharge those conditions against the exact ordered local
roots. All commands run, including unused commands before or after conflict.
Root order, unsplit premise clauses, fresh outputs, live reads, canonical
expected results, fallback rejection, conflict checks, and scope handling
retain their existing checks. `Checker_Ext`, EUF, CNF, compiler, CPC source
rules, and the shared registration/dune files are unchanged.

Untrusted search recognizes positive atomic equalities with matching endpoint
types, and positive `Fiff` over two positive Boolean `Fatom` operands. It uses
these conditional graph edges for application congruence. Boolean auxiliary
equalities use `Fiff`, without synthetic Boolean `BO_eq` atom extensions.
Boolean paths are proved through CNF and checked resolution; ordinary atomic
paths retain `EqTr`. A congruence requiring the new representation emits
`BoolCongr`; existing congruences retain the core operations when possible.
The verified bridge checks actual interpreted types independently: default
`true` from non-Boolean projection cannot establish argument equality.

No budgets, compiler options, rule names, source-rule implementations, whole
goal acceptance paths, synchronous certificate reuse, actual sigma threading,
final `exact_check`, or default fuel 10000 were changed. No new assumptions,
proof holes, array extensionality uses, system installs, pushes, PRs, or
GitHub comments are introduced.

## Tests and reproducible commands

All commands run from this worktree root. The only Rocq/OCaml wrapper is
`/home/charles/code/friends/.toolchains/smtrocq-env`. Public proofs use the
unchanged private cvc5 1.4.2 runner, its pinned binary/signature and existing
resource limits (65s wall, 60000ms solver, 10000000 resources, 32MiB output).
Search defaults remain 4096 clauses, 100000 resolution pairs, 32 theory
rounds, 128 terms, 256 formulas, 64 LIA literal visits.

The new public suite is `unit-tests/eunoia_uf_bool.v`. Shared `unit-tests/dune`
registration belongs to the parent; the suite is compiled independently here.
It has eleven live public positives and three false-statement rejection
controls. Every positive uses `cvc5_eunoia`, with `Print Assumptions` on each.
It covers the original Bool→Bool goal, Bool→Z, mixed/unchanged arguments,
nested functions, false-valued variables with an explicit equality edge,
Boolean transitivity feeding congruence, conditional congruence, compound
Boolean arguments, and a nested predicate.

`EunoiaLocalTests.v` adds twenty typed gate cases, including accepted
Bool→Bool/Bool→Z/mixed congruence, missing/wrong/signed/out-of-bounds references,
wrong types/results, missing conditions, noncanonical results, overwritten or
out-of-bounds outputs, changed roots, and unused bad commands before and after
conflict. A valid unused command after conflict is also accepted.

Native witness tests retain the complete 79-case suite and add sixteen
Boolean UF cases (eleven positive, five negative). The real gate probe now
constructs function tables with actual signatures and total denotations,
typechecks every serialized candidate and requires `Atom.wt = true` before
running the gate. It corrupts capacity, ordered roots, expected clauses,
premises, conclusions, congruence evidence (including `BoolCongr`), and
Micromega evidence. This avoids the old empty/default-Boolean table masking
actual type mismatches.

```sh
/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2 \
  theories/checker/eunoia/EunoiaLocal.vo \
  theories/checker/eunoia/EunoiaLocalTests.vo @install
/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2 \
  theories/checker/eunoia/EunoiaLocalTests.vo src/eunoia_witness/tests
/home/charles/code/friends/.toolchains/smtrocq-env \
  _build/default/src/eunoia_witness/tests/search_tests.exe
bash src/eunoia_witness/tests/verify-local-gate.sh \
  "$PWD/theories/checker/eunoia/EunoiaLocal.v"
```

The first two final builds exit 0; logs `/tmp/bool-focused-build.log` and
`/tmp/bool-tests-build3.log`. Native replay exits 0 (95 cases), log
`/tmp/bool-native-final.log`; native old79 also exited 0, log
`/tmp/bool-native-old79.log`. Real typed VM replay exits 0 (95 cases), log
`/tmp/bool-realtypedgate.log`, complete artifacts and gate assumption prints
`/tmp/smtrocq-witness-probe.9NU86E/`. The copied gate SHA256 is
`2fbbe3695659184b8041803d830c2051dd10b03964e363525db2720790f59333`.

Development builds 1–8 (`/tmp/bool-local-build*.log`) exposed and then corrected
proof-script errors; test builds 1–2 exposed and corrected a test-name clash
and OCaml module qualification errors. No failing run is counted as a
positive. A redundant concurrent `dune exec` and initial public build were
interrupted (130); `dune runtest` also once failed with `RPC server not running`.
The direct native run and final independent public compiles supersede those
invocations. No limits were raised.

Public loadpaths are computed by the existing
`tools/eunoia-profile/run.py:loadpath()`; this reads the theory stanzas and
supplies all `-Q _build/default/... logical.name` flags. The independent
public driver, exact expanded argv, sources, logs, and results are retained
in `/tmp/final_bool_suite.py`, `/tmp/bool-public-final/command.json`, and
`/tmp/bool-public-final/`. Raw one-theorem probes and their exact argv/exit
codes are in `/tmp/run_bool_cases.py`, `/tmp/bool-public-cases/results.json`,
and `/tmp/bool-public-cases/*.log`. Each raw probe has a 60s external timeout;
the suite has a 180s external timeout. The public original goal separately
exited 0, source `/tmp/BoolOriginal.v`, log `/tmp/bool-original.log`.

## Remaining raw public failures and concrete handoff

These positive goals are **not** disguised as `Fail` tests in the public suite.
Their exact sources and logs are retained under `/tmp/bool-public-cases/`:

* `positive_predicate` and `negative_predicate` (exit 1):
  `a=b -> p a=true -> p b=true`, respectively false-valued predicate results.
  Generated CPC validation rejects `@p5 (skolem_intro)`, argument
  `(@purify op_0)`. Native local predicate candidates and the typed gate pass.
* `disjunctive` (exit 1): `(a=b \/ a=c) -> (f a=f b \/ f a=f c)`.
  Generated CPC validation rejects `@p3 (eq-symm)`, arguments
  `(op_1 (@purify op_0)) (op_1 (@purify op_2))`.
* `false_inputs` (exit 129): `a=false -> b=false -> h a=h b`.
  The existing reifier raises the assertion at
  `src/common/smtlib2_genConstr.ml:421`. The version additionally supplying
  `a=b` passes as `bool_uf_false_inputs_with_edge`.
* `bool_constant` (exit 1): `a=false -> f a=f false`.
  The private solver runner reports CPC parse failure at line 1:1,
  `expected parenthesized list`, with empty stderr.

The first two are a concrete purified-term/source-rule handoff for the parent
or compiler owner. This implementation makes no compiler or source-rule edits.
The bridge itself intentionally rejects signed/constant/compound `Fiff`
operands without positive Boolean atom views; compound public arguments can
nevertheless pass when existing reification supplies suitable atoms.

## Assumption and kernel audits

Test handoff commit: `bea2dab`. The baseline file has exactly 52 qualified
names. These final audits all exit 0 and report no names beyond it:

```sh
python3 tools/audit-eunoia-assumptions.py \
  --import SMTCoq.checker.eunoia.EunoiaLocal \
  --theorem EunoiaLocal.execute_core_binding \
  --theorem EunoiaLocal.execute_bool_binding \
  --theorem EunoiaLocal.execute_valid --theorem EunoiaLocal.run_valid \
  --theorem EunoiaLocal.gate_correct --output-dir /tmp/bool-local-assumptions
python3 tools/audit-eunoia-assumptions.py \
  --import SMTCoq.checker.eunoia.EunoiaTactic \
  --import SMTCoq.checker.eunoia.EunoiaScopedAdapter \
  --theorem EunoiaTactic.checker_correct \
  --theorem EunoiaTactic.checker_b_correct \
  --theorem EunoiaTactic.checker_eq_correct \
  --theorem EunoiaScopedAdapter.checker_correct \
  --output-dir /tmp/bool-main-assumptions
python3 /tmp/final_bool_suite.py
python3 /tmp/audit_bool_helpers.py
```

The final suite driver compiles the exact new public source independently
as `EunoiaBoolPublic.BoolUF`, then calls the assumption auditor with all
fourteen exports. Expanded command/flags and logs are in
`/tmp/bool-public-final/command.json`, `/tmp/bool-public-assumptions/summary.json`,
and `/tmp/bool-public-final-driver.log`. The suite and public-export audit
both exit 0. The driver's initial helper walk tried the three negative
control proofs, which intentionally have no saved checker certificate, and
exited 1 at the first such control. The final helper-only driver limits its
walk to all eleven successful public tactic proofs: it exits 0 and verifies
all saved VM certificate bodies with the existing `Eunoia_helper_assumptions`
body walker. Its eleven reports contain a union of 17 baseline names and no
additions. Final log `/tmp/bool-helper-audit.log`, exact helper command
`/tmp/bool-public-final/helpers-final-command.json`, machine-readable summary
`/tmp/bool-public-final/helpers-summary.json`. The local, main, and whole
public-export audit unions each equal the full 52-name baseline.

The independent recursive kernel check exits 0 with an empty diagnostic log
`/tmp/bool-recursive-check.log`:

```sh
/home/charles/code/friends/.toolchains/smtrocq-env rocq check -silent \
  -Q _build/install/default/lib/coq/user-contrib/SMTCoq SMTCoq \
  -Q /tmp/bool-public-final EunoiaBoolPublic \
  SMTCoq.checker.eunoia.EunoiaBoolTests \
  SMTCoq.checker.eunoia.EunoiaLocalTests EunoiaBoolPublic.BoolUF
```

It checks dependencies recursively with neither `-admit` nor `-norec`.
The exact suite source matches `/tmp/bool-public-final/BoolUF.v` byte for
byte. The pinned solver/archive/signature verification also exits 0:

```sh
python3 -B scripts/eunoia/verify_toolchain.py \
  --toolchain-root /home/charles/code/friends/.toolchains
```

Log `/tmp/bool-toolchain-verification.log`. Final `git diff --check` exits 0;
the changed Coq source scan has no proof holes, new declarations of axioms or
parameters, aborted proofs, or `array_ext` references.

## Existing public suites and freeze

The final wrapped build of the unchanged UF22 and LIA15 suites exits 0:

```sh
timeout 240 /home/charles/code/friends/.toolchains/smtrocq-env dune build -j2 \
  unit-tests/eunoia_uf.vo unit-tests/eunoia_lia.vo
```

Log `/tmp/bool-old-public-build-final.log`. The 240s outer process cap did not
fire. Both `.vo` files were produced, including their existing negative
controls and assumption prints. There were no source or budget edits to these
suites. The initial redundant attempt, interrupted at 130 as noted above,
is retained in `/tmp/bool-old-public-build.log`.

The source and artifact SHA256 freeze is committed separately in
`docs/eunoia/boolean-uf-integration-hashes.json`: fifteen sources (including
both authorized bridge files, the baseline, and all three public suites)
and nine compiled artifacts (including both existing public suites and the
new suite). These hashes describe this worktree's final bytes; they are not
an expectation of bit-identical `.vo` output after a parent rebuild.

Parent-only registration handoff: add `eunoia_uf_bool` to the explicit module
list in `unit-tests/dune`, and add `EunoiaBoolTests.vo` to the existing checker
runtest alias in `theories/checker/eunoia/dune`. Both modules compile here
without those shared-file edits; the existing checker theory discovers and
installs `EunoiaBool` automatically. No parent shared file was written.

The unchanged UF22/LIA15 artifacts also pass their independent recursive
kernel check (exit 0, empty `/tmp/bool-old-public-recursive-check.log`):

```sh
/home/charles/code/friends/.toolchains/smtrocq-env rocq check -silent \
  -Q _build/install/default/lib/coq/user-contrib/SMTCoq SMTCoq \
  -Q _build/default/unit-tests SMTCoq.tests \
  SMTCoq.tests.eunoia_uf SMTCoq.tests.eunoia_lia
```

All required child-owned validation is complete. The raw positive failures
listed above remain rejected, and the parent-only shared registration is the
remaining integration handoff.
