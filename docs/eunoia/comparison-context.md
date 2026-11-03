# Lean-SMT and Sledgehammer comparison context

Research/access date: **2026-11-03**. Repository base:
`de38af7662adcaa589f46c7b67cabe58bd741dfe`, child branch
`t3/eunoia-comparison-context` (initial name: `t3/d5651c1f`).
This document supplies external context for the coordinator's eventual PR body;
it does not establish completion or competitive performance of this port.

**Usable PR conclusion:** published Lean-SMT and Isabelle results concern
different workloads and measurement boundaries. No matched local Lean-SMT or
Sledgehammer run is available. The cvc5/Eunoia integration still needs final
checked measurements; neither a speed ratio nor a ranking against those systems
is supported by the evidence below.

## Identify the systems and their trust boundaries

* **Lean-SMT means `ufmg-smite/lean-smt` here.** The
  [paper's project link](https://link.springer.com/chapter/10.1007/978-3-031-98682-6_11#Fn2)
  identifies this repository.
  Its `smt` tactic sends translated goals to cvc5 and reconstructs proofs in
  Lean. Its advertised fragments are UF and linear integer/real arithmetic,
  including quantifiers; bit-vector support is experimental. Optional
  `lean-auto` monomorphization reduces richer goals to first-order logic.
  Unsupported proof steps remain obligations, so invocation without closing
  every obligation is insufficient. See the [pinned README](https://github.com/ufmg-smite/lean-smt/blob/db545bebe2de1e06dc2df62a6ff6c20e5736bfc0/README.md).
  The paper describes cvc5's CPC calculus, accessed through its API, and
  reconstruction into kernel-checked Lean terms; classical choice can be used.
  [Paper, §3](https://arxiv.org/html/2505.15796v1#S3).
  Current source defaults to `trust := false`, `native := false`; enabling
  native reconstruction adds the Lean compiler to the trusted base, while
  enabling trust bypasses proof reconstruction. These modes must be recorded
  separately in any future comparison. [Tactic configuration and implementation](https://github.com/ufmg-smite/lean-smt/blob/db545bebe2de1e06dc2df62a6ff6c20e5736bfc0/Smt/Tactic/Smt.lean#L36),
  [unhandled-step obligations](https://github.com/ufmg-smite/lean-smt/blob/db545bebe2de1e06dc2df62a6ff6c20e5736bfc0/Smt/Reconstruct.lean#L175).
* **Sledgehammer is a portfolio and premise-selection tool**, rather than one
  SMT checker. It can suggest internally replayed `metis`, `smt`, or simpler
  Isabelle proofs after external search. A successful search message and the
  timing printed for a suggested proof method have different meanings.
  [Pinned user guide, introduction and example](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/Doc/Sledgehammer/document/root.tex#L104).
  Relevant SMT routes support equality/UF, quantifiers and integer/real
  arithmetic, with translation and reconstruction limitations. Current source
  includes Alethe replay for veriT and cvc5, and Z3-specific replay. With
  `smt_oracle = false`, the proof must be reconstructed inside Isabelle/HOL;
  oracle results are unsuitable as checked proofs. The source explicitly sets
  that option false and cvc5's proof format to Alethe. This boundary relies on
  Isabelle's inference kernel and HOL foundations, rather than correctness of
  an external `unsat` answer. [SMT theory, encodings and replay modules](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/SMT.thy),
  [proof-production settings](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/SMT.thy#L1114).
* **This port** targets signature-generated CPC checking through existing
  SMTCoq interpretations and verified EUF/LIA checkers, followed by a Rocq
  proof. Initial target fragments are QF_UF/QF_LIA; actual accepted coverage
  must come from completed integration tests. No solver-only success counts as
  a checked theorem. See [implementation-plan.md](implementation-plan.md) and
  the [local measurement protocol](../../benchmarks/eunoia/README.md).
* **Logos is a separate Lean-based Eunoia checker**, not the Lean-SMT tactic.
  Its [README](https://github.com/cvc5/logos) and the
  [2026-10-23 performance issue #485](https://github.com/cvc5/logos/issues/485)
  concern that checker. The historical Logos/Ethos factor discussed in the
  [existing pinned survey](logos-design.md#issue-485-read-before-the-source-survey)
  cannot be transferred to Lean-SMT, Sledgehammer, or this port. No local Logos
  or Ethos build/run was used here. If a different Lean tactic was intended,
  its identity and protocol need explicit selection; the name `smt` alone
  does not identify an implementation.

## Source versions versus versions actually measured

These are inspected source pins, **not installations or reproduced paper
configurations**:

| Source | Immutable revision and date | Relevant version information |
| --- | --- | --- |
| Lean-SMT | [`db545bebe2de1e06dc2df62a6ff6c20e5736bfc0`](https://github.com/ufmg-smite/lean-smt/commit/db545bebe2de1e06dc2df62a6ff6c20e5736bfc0), committer date 2026-10-20 | [Lean 4.34.0](https://github.com/ufmg-smite/lean-smt/blob/db545bebe2de1e06dc2df62a6ff6c20e5736bfc0/lean-toolchain); [manifest](https://github.com/ufmg-smite/lean-smt/blob/db545bebe2de1e06dc2df62a6ff6c20e5736bfc0/lake-manifest.json) pins `lean-cvc5` at `41e47796d4d15712e6064b064ca5d251a1283955`. That binding's [build definition](https://github.com/abdoo8080/lean-cvc5/blob/41e47796d4d15712e6064b064ca5d251a1283955/lakefile.lean#L21) selects its fork's `cvc5-1.3.2` release. This is not our cvc5 1.4.2 binary. |
| Isabelle development source, official mirror | [`f86f290225eebcc52c1ae7dba2e098f405f51c21`](https://github.com/isabelle-prover/mirror-isabelle/commit/f86f290225eebcc52c1ae7dba2e098f405f51c21), committer date 2026-10-31 | [Component manifest](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/Admin/components/main): cvc5 1.3.4, veriT 2026.05, Z3 4.4.0pre-8. Development source is distinct from the [Isabelle2025-2 release, January 2026](https://isabelle.in.tum.de/website-Isabelle2025-2/index.html). |

## Published measurements: context, not a local comparison

Mohamed et al., *Lean-SMT*, CAV 2025, published **2025-07-23**,
[DOI 10.1007/978-3-031-98682-6_11](https://link.springer.com/chapter/10.1007/978-3-031-98682-6_11).
The [2025-05-21 preprint, arXiv:2505.15796v1, Appendix B](https://arxiv.org/html/2505.15796v1#A2)
provides explicit counts:

| Dataset | Complete checked proofs, excluding holes |
| --- | --- |
| 5,000 Sledgehammer-generated SMT-LIB problems | cvc5 + Lean-SMT: **2,847**; veriT + Sledgehammer: **2,180** |
| 11,804 quantifier-free SMT-COMP 2024 problems | cvc5 + Lean-SMT: **4,869**; veriT + SMTCoq 2.2: **4,178** |

The preprint also counts checking with holes; those larger counts are not
complete proofs. The QF subset mixes UF, difference logics and linear
integer/real/mixed arithmetic. §4.2 uses a 20-minute timeout and solving-plus-checking
curves; replay-only times are separate. §4.1's timeout is unspecified.
SMT-LIB input does not establish native preprocessing/import costs.
Reported hardware: Ryzen 9 7950X, 4.50 GHz, 128 GB/node; footnote 6 specifies
48 processors per node. Measured Lean/cvc5/veriT/Isabelle revisions are
unspecified; today's pins cannot identify them. [Preprint §4 and tables](https://arxiv.org/html/2505.15796v1#S4).

Lachnitt et al., *Improving the SMT Proof Reconstruction Pipeline in
Isabelle/HOL*, ITP 2025, published **2025-09-22**,
[DOI 10.4230/LIPIcs.ITP.2025.26](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2025.26):

* §6.1/Table 2, 5,000 AFP-derived goals with at most 512 selected facts:
  cvc5/Alethe reconstructed **2,869**, veriT/Alethe **2,608**. Average
  reconstruction-only times on commonly solved problems were **874 ms** and
  **246 ms**, respectively. Solver/proof printing had a five-minute limit;
  reconstruction had 20 minutes. Hardware: Xeon E5-2637 v4, 8 GB/job.
* §6.3, HOL Library calls selected by Sledgehammer/Mirabelle: **267** `smt`
  queries, with **257** successes using veriT, **119** Z3, **243** cvc5.
  The entire `smt` call had ten seconds. Hardware: i9-12900, 128 GB RAM,
  three concurrent Mirabelle instances, 30 GB ML limit.

These are different populations and timing boundaries. The paper does not
provide exact measured solver/Isabelle commit pins; its mention of veriT
2024.12 is not a complete experimental version manifest. Neither experiment
is a per-fragment QF_UF/QF_LIA evaluation of our goals.
[Paper §6, tables and protocol](https://drops.dagstuhl.de/storage/00lipics/lipics-vol352-itp2025/html/LIPIcs.ITP.2025.26/LIPIcs.ITP.2025.26.html).

The underlying [*Seventeen Provers Under the Hammer*, DOI
10.4230/LIPIcs.ITP.2022.8, published 2022-08-03](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2022.8)
is the dataset lineage, not a measurement of this backend. Premise selection,
encoding and fact-count choices must match before comparing runs. None of
these publications yields a speed ratio for the custom Rocq suite.

## Existing local evidence and what must be rerun

Read-only evidence directory:
`/tmp/smtrocq-eunoia-baseline-20261103-946ad9fd/`, especially `report.txt`,
`results.json`, `results.csv`, `summary.json`, and `metadata.json`.
Measured clean source: `bcf01136a63a9b621b4bf1d83f7eb2e8bd543f9f`.
The recorded command (not rerun in this research job) was:

```sh
python3 benchmarks/eunoia/run.py --backends verit cvc4 --repeat 3 --timeout 30 --jobs 2 --output /tmp/smtrocq-eunoia-baseline-20261103-946ad9fd
```

It exited **1** for backend failures. On six integer-carrier UF-shaped and six
LIA positive goals, three repeats: veriT checked **36/36** attempts, CVC4
**3/36**, all for `uf_congruence`; each rejected six negative attempts.
Versions: Rocq 9.3.0, OCaml 4.14.2, Dune 3.21.1, veriT `dev`, CVC4 1.6.
The recorded platform is WSL2/Linux x86-64; no CPU/RAM specification was
recorded. Successful tactic medians were 0.077 s and 0.085 s on **different
solved populations**; they support no aggregate speed ranking.

`Time backend` includes preprocessing, solver interaction and checked tactic
computation; `Time Qed` is separate. Compiler wall time includes startup,
imports and the assumption audit. The 30-second timeout covers the compiler
process, not only the solver. Success requires completed `Qed`, a fresh `.vo`
and the final assumption-audit marker. See the [harness protocol](../../benchmarks/eunoia/README.md).
The baseline predates the added abstract-carrier cases: its denominator is
12 positives, not the current 18.

The historical `/tmp/smtrocq-first-cvc5-eunoia-live-benchmark/` checked **1/12**
positives; it is an integration diagnostic, not final performance.
`/tmp/smtrocq-abstract-uf-development-benchmark/summary.json` has **0/6** cvc5
successes and null successful latency fields, exposing the proof-local carrier
universe problem described by the coordinator. Failed transactions supply no
valid successful-proof timings. Both runs remain provisional pending final
measurements; no failed-attempt timing or unmatched solved-time sum is used here.

For a defensible comparison, the coordinator would need to:

1. Finish integration and rerun every backend on the same versioned manifest,
   recording checked successes/failures and inherited assumptions.
2. Port identical source goals and explicit premises into Lean and Isabelle,
   preserving `Z`/`Int`/`int`, Boolean versus propositional presentation, and
   inhabited carrier assumptions (`CompDec`, Lean `Nonempty`, HOL sorts).
   Install/import pinned Lean-SMT and Isabelle privately before any local run.
3. Measure full native tactics with closed, audited proofs; record solver-only,
   reconstruction, final checking and process times separately, with common
   limits, hardware, versions, repeats and comparable cache conditions.
   Analyze latency only on the common solved set and report coverage separately.
4. For published-corpus claims, obtain the exact SMT-LIB/fact-selection corpus
   and artifact versions, import it into each checker, and enforce complete
   proofs without holes or oracle modes. SMT-LIB replay alone would still not
   measure each assistant's native goal preprocessing.

No aligned data warrants a comparative chart. Final cvc5 measurements, native
Lean/Isabelle ports and paper-artifact reproduction remain incomplete and
belong to the coordinator; this job ran no new backend benchmarks.

## Research commands and validation

All local reads were confined to named repository files and supplied evidence
paths. Principal commands (exit **0**, unless stated otherwise):

```sh
git branch --show-current
git rev-parse HEAD
git log -6 --format='%h %s'
cat BEST_PRACTICE.md ARCHITECTURE.md docs/eunoia/implementation-plan.md
cat benchmarks/eunoia/README.md scripts/eunoia/README.md
cat /tmp/smtrocq-eunoia-baseline-20261103-946ad9fd/report.txt
cat /tmp/smtrocq-eunoia-baseline-20261103-946ad9fd/results.json
/home/charles/code/friends/.toolchains/smtrocq-env bash -c 'for tool in lean lake isabelle rocq ocaml dune; do if path=$(command -v "$tool"); then printf "%s: %s\n" "$tool" "$path"; else printf "%s: unavailable (command -v exit 1)\n" "$tool"; fi; done'
```

The availability command exited **0**: `lean`, `lake`, `isabelle` each had
`command -v` exit **1**; `rocq`, `ocaml`, `dune` resolved under
`/home/charles/code/friends/.toolchains/opam/smtrocq/bin/`.
This is a wrapped-PATH observation, not a machine-wide installation search.
`rg --files --hidden -g 'AGENTS.md' -g '!\.git' -g '!_build' .` exited **1**
(none found); explicit ancestor `AGENTS.md` checks also found none.

Exact initial `web.run` search queries:

```text
Lean-SMT lean tactic GitHub paper SMT proof reconstruction
Sledgehammer SMT reconstruction Z3 veriT benchmarks paper Isabelle
"Lean-SMT: An SMT" site:link.springer.com/chapter
```

Paper and project pages were opened with `web.run.open`; pinned files were
read through raw GitHub URLs. Paper sections/tables and dates were inspected
directly. GitHub history web results were stale, so current source pins came
from these read-only API URLs:

```text
https://api.github.com/repos/ufmg-smite/lean-smt/commits/HEAD
https://api.github.com/repos/isabelle-prover/mirror-isabelle/commits/HEAD
https://api.github.com/repos/abdoo8080/lean-cvc5/commits/41e4779
```

Python `urllib.request.urlopen(url, timeout=30)` reads succeeded (command exit
**0**) after network escalation; the initial sandboxed request exited **1**
with DNS resolution failure. Selected pinned raw source copies are retained in
`/tmp/smtrocq-comparison-research/`; no dependency was installed. The official
Sledgehammer PDF timed out in the web tool, so its pinned source in the official
GitHub mirror was used instead. Sources were checked for adjacent attribution,
measurement definitions and complete-proof denominators; no numerical graph
was digitized or inferred.

Additional link check:
`python3 /tmp/smtrocq-comparison-research/validate_links.py` exited **1**:
**22/23** cited external URLs fetched with HTTP 200 (GitHub files via raw
content; commits via API). The release-index URL was unreachable from the shell;
its release/date information was available in the official-site web search
result. Receipts: `/tmp/smtrocq-comparison-research/link-validation.json`.
Relative citation targets and whitespace passed the Python read-only check
(exit **0**). `git diff --cached --check` also passed (exit **0**) before the
local commit. Staging required filesystem escalation because this worktree's
Git index lives outside the writable worktree; the first `git add` exited
**128** with a read-only index-lock error.

No source/build/shared file changes, new lemmas, or new assumptions were made.
`Print Assumptions` is inapplicable to this documentation-only change. No push,
PR, GitHub comment or other publication is authorized or performed.
