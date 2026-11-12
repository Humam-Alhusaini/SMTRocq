# Independent review of checked-certificate reuse

## Verdict and exact scope

No new P0–P2 finding in the bounded code, installed-API and proof/test scope
below. This is not an overall port-completion, benchmark, or general Rocq
soundness verdict.

Reviewed commits:

* `b7e77ff21332d04187183bbf416948168a5d0a55`
  (developer probes and saved-body assumption query).
* `ed9d8aae105728ed4185ff404cb5f1f5fae83e9e`
  (same-invocation checked-certificate reuse and candidate report).
* Candidate base: `604c0438c70d257f666538e498e187eb691898a1`.
* Prepared review parent: `8a739b72d5fe994690035bc33740e5fe5ab74524`.
  The candidate was merged locally for reproduction as
  `3792b7b3465ae5c1a755fc70971412106d0860d3`.

I read `checked-certificate-reuse.md`, the handoff at
`/tmp/eunoia-proof-reuse-handoff.json`, both commit diffs, the complete affected
backend paths, the mutation fixtures, and the probe/audit drivers. No production
code, shared Dune file or tactic/theory source was edited during review. This
review's authored commit contains only this document; the local merge imports
the already authored candidate commits.

The parent subsequently reported integration at `4f87e02`, with a default
Controls test alias and an explicit test-plugin declaration in `audit_helpers`.
Those parent-only changes were not rebased into or independently reviewed here.
The parent reports no production backend/theory difference. Its new full UF22 /
LIA15 runs are separate evidence, not results claimed by this review. The stated
49-rule / 53-helper generated coverage and prior 52-assumption full audits are
context, not fresh coverage measurements here.

## Why the private helper is checked before reuse

The reviewed backend is `src/eunoia_backend/eunoiaBackend.ml`, SHA-256
`17e7ee41a311e72b168bfc8b7bef33d7cd474521f206ac69c2001a456a3e6b99`.
Installed toolchain: Rocq **9.3.0**, OCaml **4.14.2**. I inspected installed
sources under
`/home/charles/code/friends/.toolchains/opam/smtrocq/lib/rocq-runtime/`, rather
than inferring behavior from the API name:

1. `tactics/abstract.ml:25–79`: `cache_term_by_tactic_then` gets the current
   Proofview environment, sigma, proof name and polymorphism status. It splits
   actual proof and Section variables, generalizes the requested type, chooses
   a fresh name against the environment and existing side effects, and wraps
   the solving tactic in `tclCOMPLETE`. It calls `Subproof.declare_abstract`
   before updating Proofview with the returned sigma and calling the callback.
2. `proofs/subproof.ml:109–137,166–221`: the subproof must be finished;
   conversion of both body and type to `Constr.t` without unresolved evars
   must succeed.
   Its universe state is retained. `drop_new_defined` preserves original evars
   and normalizes away newly defined subproof evars; `shrink_entry` removes
   unused generalized arguments, not proof obligations. The opaque entry
   contains the actual body, exact type, universe entry and Section context.
3. `engine/evd.ml:1280–1303`: `push_side_effects` calls
   `Safe_typing.add_private_constant` before returning the new private effects.
   It builds a safe environment stored in the sigma's side effects; this is not
   a backend call to mutate `Global` or declare an axiom.
4. `kernel/safe_typing.ml:1085–1093,1272–1312`: the opaque branch calls
   `infer_direct_opaque`, which calls `Constant_typing.check_delayed`
   **immediately**, with a handler returning zero trusted effects.
   `kernel/constant_typing.ml:267–300` infers the body and checks its type and
   Section-variable use. `kernel/typeops.ml:334–347` sends VM casts through
   `Vconv.vm_conv`. No future or postponed body evaluation intervenes here.
5. Only after that check does Rocq create the private certificate and permit
   the proof environment's body-less representation (`Undef None`) of the
   opaque constant. The checked body remains in the side effect. That
   representation is not an unchecked exported assumption.

At saving, `safe_typing.ml:922–988,1215–1230` inlines private bodies into the
saved main proof: opaque monomorphic bodies as lambda applications, polymorphic
bodies by substitution. Signature validation (`safe_typing.ml:1005–1038`) and
`constant_typing.ml:75–97` allow already checked monomorphic helper bodies to
be skipped at this later check. An invalid/missing signature does not grant
that skip. Polymorphic substitution need not save this later computation.
The optimization uses Rocq's existing checked-proof mechanism; it introduces no
backend trust flag, custom certificate, unchecked declaration, or detached work.
The driver starts `Time`/profiling around the complete tactic, before preparation,
helper creation and synchronous checking, then times `Qed` separately. Its
process CPU/wall accounting includes compiler startup/imports. Thus helper work
has not been moved outside those measurement boundaries. The independent
recursive check intentionally repeats validation and is reported separately.

An independent temporary API probe supplied a VM cast claiming `false = true`
using `exact_no_check` **only inside the test sub-tactic**, deliberately forcing
the private declaration to provide the kernel check. The reuse callback set an
observable flag; the surrounding test required that flag to remain false and
that the proof sigma contain no private effects. Compilation passed, and the
log records the expected `eq_refl : true = true` versus `false = true` error.
This tests synchronous kernel rejection beyond the production sub-tactic's
own `exact_check`. No invalid body was accepted or saved.

## Complete inputs, context, and public contract

* `prepare` (`eunoiaBackend.ml:127–288`) is unchanged. It elaborates every
  command; ordinary and scoped steps retain rule arguments, premise syntax,
  source result, conclusion, local witness and slot/premise identifiers.
  Scope discharges retain the actual pushed literal and endpoint. The final
  table snapshot follows all result/witness interning. The naming, fuel,
  capacity, root terms, claims, complete trace and conflict remain arguments.
  `EunoiaChecker.run:180–189` and `EunoiaScope.run:80–105` traverse the complete
  trace, including supported steps unused by the final conflict.
* `with_checked_acceptance` (`:308–322`) forms precisely
  `@eq bool computation true`, with the **complete applied checker** as
  `computation`. It supplies the VM cast to `Tactics.exact_check` inside opaque
  abstraction. There is no Boolean-success cache, lookup key, cross-invocation
  memoization, reduced witness/trace, or lowered fuel.
* The no-lemma branch (`:358–365`) retains all `common_args`, the exact Boolean
  result or equality literal arguments, and all `tail_args` for `checker_b` or
  `checker_eq`. It uses the corresponding concrete correctness theorem and
  finishes with `exact_check`.
* The supplied-lemma branch (`:367–401`) uses all roots, including duplicates,
  and the same complete `checker` arguments. Its correctness application and
  `Forall` proof retain the actual supplied proofs. Tables and proofs are still
  lifted below the false-equality binder. The final assembled proof passes
  `exact_check`; the removed intermediate check was redundant on this tactic
  path. The concrete correctness wrappers still fix `EunoiaLocal.gate` and
  generated default primitives; no generic unproved gate is substituted.
* `refutation`, `build_refutation_from_cpc` (`:290–302`) and
  `build_refutation` (`:407–411`) are unchanged. The public builders still run
  `checked_true`, `Typing.type_of` on the complete refutation and write the
  returned constraints through the supplied actual sigma reference. Their
  interface contract and arguments did not change.
* Tactic entry retains current proof-local universe constraints (`:325–329`).
  Abstraction returns its updated sigma through the standard API. The callback
  converts `lemma args` using **the callback goal's current sigma** (`:315–318`);
  final `exact_check` also reads and updates the current sigma. There is no
  restoration of a stale pre-abstraction map or new CompDec evar. Existing
  missing-instance rejection remains in force. The focused sibling-evar and
  polymorphic Section tests below supplement this source inspection; they do
  not claim exhaustive testing of all evar/universe configurations.
* `tclORELSE` invokes diagnostics on failure and then fails again. Diagnostics
  may replace an error or redo computations on a rejected path; they cannot
  accept a certificate. There is no new backend global mutation. I checked
  successful-helper rollback through both a failing vernacular command and
  actual Proofview backtracking, in addition to the candidate's Undo control.

The candidate's earlier exact-input comparison artifacts cover congruence,
supplied roots and scoped arithmetic and agree with this source analysis. I
read those artifacts but did not rerun their temporary production-source
instrumentation, respecting the review's no-production-edit boundary.

## Independent execution and assumptions

All Rocq/OCaml commands used the private wrapper
`/home/charles/code/friends/.toolchains/smtrocq-env`; the live backend selects
cvc5 1.4.2 through its absolute path in `eunoiaSolver.ml:13–15`. Default checker
fuel was 10000, unchanged. The proof-compilation and kernel-check drivers
record their timeout caps; none of the final validation commands timed out.
Their `command.json` files contain full argv, cwd, exit and measured CPU/wall
values, with adjacent `output.log`. The standalone wrapper-assumption audit
and temporary plugin compilation were not given timeout caps.

```sh
python3 -B tools/eunoia-proof-reuse/run.py \
  --output /tmp/eunoia-certificate-review-run2 --helpers --controls --timeout 120
python3 -B tools/eunoia-proof-reuse/verify.py \
  --profile-dir /tmp/eunoia-certificate-review-run2 \
  --output /tmp/eunoia-certificate-review-validation
```

The first command exited **0**. Its nine positives are quantified abstract
congruence, positive and negative predicates, two sorts with an intermediate
CompDec instance, repeated supplied hypotheses `(Hxy, Hyz, Hxy)`, live integer
bound conflict, arithmetic normalization replay, scoped arithmetic replay, and
nested scope export essential to the refutation. Every case closed with `Qed`
and passed the ordinary main-theorem and saved-cast dependency audits.
`run2/results.json`, `metadata.json` and each case's `command.json` retain the
exact sources, commands, plugin hashes and timings. All 50 recorded plugin/
theory artifact hashes matched at run start/end.

The second command also exited **0**. It rebuilt the plugins, recompiled all
nine positives plus Controls into 17 exports, audited all 17 main theorems and
15 saved-cast dependency unions, and recursively kernel-checked the aggregate.
The 15 tactic-generated main proofs each have exactly the baseline's 52 names;
the missing-instance and false-control exports are closed under the global
context. Every saved-cast dependency union has 17 baseline names. Compilation
took 36.466 wall seconds, the main audit 14.849, the saved-body audit 4.574,
and the recursive check 39.579 (39.470 user, 0.232 system). All exited **0**,
with no timeouts at their 120-second caps. The 48 hashed theory/validation
`.vo` files were identical before and after the kernel check. Full results:
`/tmp/eunoia-certificate-review-validation/status.json`,
`audit/summary.json`, `helpers/summary.json`, and the stage `command.json`/
`output.log` files.

The actual kernel command is recorded in `kernel/command.json` and has the
following form, where `LOADPATHS` is the exact list of `-Q` arguments from
`tools/eunoia-profile/run.py:loadpath` retained in that JSON:

```sh
/home/charles/code/friends/.toolchains/smtrocq-env rocq check \
  -silent -bytecode-compiler yes LOADPATHS \
  -Q /tmp/eunoia-certificate-review-validation EunoiaProofReuseValidation \
  EunoiaProofReuseValidation.Validation
```

There are no dependency-admission flags. This is a new compiler/kernel run in
the review worktree, not a reading of the candidate's earlier successful log.

`Controls.v` compiled with exit **0** and its eight exports/six saved-body
audits passed. It tests corrupted used and unused Boolean witnesses, supported
unused scoped witnesses, corrupt discharge evidence, arithmetic source
coefficient/premise/result/root changes, missing used/unused Micromega evidence,
scope binding/leak/endpoint rejection, missing intermediate CompDec, false
arithmetic and false injectivity controls, Undo, and universe-polymorphic
Section discharge. Failure controls check both private proof effects in sigma
and absence of the expected helper name; the sigma check is the substantive
rollback oracle. An unsupported unused `trust` command is also rejected; that
control alone would not establish rejection of corrupted supported steps.

Temporary independent probes live entirely in
`/tmp/eunoia-certificate-review-extra/` (`g_review.mlg`, generated `g_review.ml`,
`certificate_review.cmxs`, `certificate_review/META`, `Extra.v`). They add:

* The direct synchronous-invalid-body API test described above.
* An exception **after** a successful checked backend replay, followed by
  `backend_no_private_effects` and successful reuse in the same proof.
* The same sequence inside `Proofview.tclORELSE`, checking private effects in
  its alternative and then replaying successfully. Both paths print
  `REVIEW_POST_SUCCESS_FAILURE`, proving the post-success failure was reached.
* An unused supported `refl` step with a mismatching explicit source result,
  then rejection, an empty-private-effects check, and a valid replay.
* A pending existential evar in a sibling goal that is subsequently solved;
  two goals using different Boolean parameters; and a successful first proof
  followed by rejection under a changed false goal/context.

The extra plugin build and final `Extra.v` compilation exited **0**.
`plugin-build.json`, `command.json` and `output.log` contain their exact
commands and evidence. These probes are review artifacts, not production
changes or new registered repository tests.
The final `g_review.mlg` SHA-256 is
`a2122740c990cc53aa65aa2b2b7185a63b54145d5b2191d2d51f793d9f53db47`;
`Extra.v` is
`40b3509f94c64a0139b8f09c41bb7afb351fa169725aa5e9c74eefcb013375cc`.

The extra module also passed a separate recursive kernel check, exit **0**
in 25.027 wall seconds (25.108 user, 0.151 system), under a 120-second cap:

```sh
/home/charles/code/friends/.toolchains/smtrocq-env rocq check \
  -silent -bytecode-compiler yes LOADPATHS \
  -Q /tmp/eunoia-certificate-review-extra '' Extra
```

The exact argv, 48 stable theory/Extra `.vo` hashes, exit, timeout and timings
are in `/tmp/eunoia-certificate-review-extra/kernel/status.json` and
`command.json`; the silent checker log is `output.log` in that directory.

For the main wrappers I ran:

```sh
python3 -B tools/audit-eunoia-assumptions.py \
  --import SMTCoq.checker.eunoia.EunoiaTactic \
  --import SMTCoq.checker.eunoia.EunoiaScopedAdapter \
  --import SMTCoq.checker.eunoia.EunoiaLocal \
  --theorem EunoiaTactic.checker_correct \
  --theorem EunoiaTactic.checker_b_correct \
  --theorem EunoiaTactic.checker_eq_correct \
  --theorem EunoiaScopedAdapter.checker_correct \
  --theorem EunoiaScopedAdapter.checker_b_correct \
  --theorem EunoiaScopedAdapter.checker_eq_correct \
  --theorem EunoiaLocal.gate_correct \
  --output-dir /tmp/eunoia-certificate-review-wrappers
```

Exit **0**: each of these seven wrappers has exactly the existing 52 names.
The baseline file SHA-256 is
`2a559618467fa69b14fea71e71f528fd7d503bfaa11baa383bef992cd688f11c`.
The same baseline is used for the actual tactic proofs and saved-body audits.
The extra module's final `audit-final/summary.json` reports seven main exports
and six saved-cast dependency audits: the API-rejection theorem is closed under
the global context, the other six main proofs have exactly 52 names, and all
six cast-dependency unions have 17 names, each a subset of the baseline.
The corresponding unabridged `Print Assumptions`/query outputs are retained as
`.out` files. No proof hole or new axiom/parameter was added.

## Audit adequacy and remaining bounds

The test-plugin query (`g_backend_test.mlg:192–215`) gets the actual saved
opaque theorem body, walks VM casts, and asks Rocq's own `Assumptions` walker
and printer about global constants/inductives/constructors found inside those
casts. The query is read-only and is not used to build a proof. It fails when
there is no VM cast, which avoids the initially incorrect expectation of an
exported helper name after `Qed` inlining.

It produces a **per-theorem union of dependencies beneath VM casts**, not a
separate theorem per helper, a cast-count assertion, or a check that every cast
has the intended checker as its head. It does not by itself audit enclosing
binders or prove complete input retention. Ordinary whole-theorem
`Print Assumptions`, source inspection and recursive kernel checking provide
the complementary evidence here. Closed local carrier/CompDec arguments are
legitimate theorem parameters, not additional global assumptions.

`verify.py:35–36` deliberately aggregates only first-repeat cases marked
`checked`; it can pass on a subset if its input run contains failures. Thus its
success alone must not be described as a full requested case matrix. Here I
separately verified that all nine requested rows and all controls passed.
The candidate helper driver also relies on these modules having loaded the
test plugin; it does not itself declare that plugin for arbitrary public
modules. The parent's reported explicit-declaration change addresses that
integration limitation and is outside the two reviewed commits.

This review does not establish a new performance comparison. It did not rerun
the full UF22/LIA15 matrix, the opt-in integer-transitive diagnostic, larger
timeout cases, or all native solver/resource controls. The candidate report's
timing variability and small nested-scope regression remain qualifications,
and prior artifacts are not substituted for fresh independent results.

## Execution record

The initially empty review worktree built the three native plugins in 1.016
wall seconds, exit **0**, but the first `run.py` invocation exited **1** because
theory `.vo`/install paths did not yet exist. Every failed case and diagnostic
is retained in `/tmp/eunoia-certificate-review-run/`; these are setup failures,
not passing validations or certificate rejections.

The required prerequisite build then ran:

```sh
/home/charles/code/friends/.toolchains/smtrocq-env dune build -j2 @install \
  src/eunoia_backend/tests/integration/backend_test_plugin.cmxs
```

It exited **0** in 114.442 wall seconds under a 180-second cap
(`/tmp/eunoia-certificate-review-install/command.json`, `output.log`). There
was no unbounded full build or unrelated benchmark run. The extra plugin's
first load attempt exited **1** due to its missing temporary Findlib package;
`first-load-failure.json`/`.log` preserve that attempt. Adding the local META
and using the package name fixed the test setup. Earlier successful extra
probe iterations are retained as `initial-success.*` and `prior-success.*`;
the final module includes the Proofview backtracking control.

Installed Rocq source hashes are retained in
`/tmp/eunoia-certificate-review-extra/rocq-source-sha256.json`. The affected
backend and new probe files still match the reviewed candidate; only this
review document is newly authored. No push, PR, external comment, system
installation, sudo, or shell-configuration edit was performed.
