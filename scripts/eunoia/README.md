# Private cvc5 / CPC capture tools

These Python 3.9+ standard-library tools provision **verification evidence** for
an existing private installation. They do not install, download, extract, modify
the toolchain, change `PATH`, or search for a system solver. The versioned
[manifest](cvc5-1.4.2.json) pins upstream download URLs and both supplied SHA256
checksums. Verification is offline and idempotent. Keep the cached archives:
installed file existence or `--version` alone is insufficient verification.

The default private root is `/home/charles/code/friends/.toolchains`. Override it
with `--toolchain-root /absolute/private/root` or `EUNOIA_TOOLCHAIN_ROOT`. System
roots are rejected. Expected paths relative to that root are:

* `downloads/cvc5-1.4.2-Linux-x86_64-static.zip`
* `downloads/cvc5-1.4.2-source.tar.gz`
* `cvc5-1.4.2/cvc5-Linux-x86_64-static/bin/cvc5`
* `cvc5-1.4.2/cvc5-cvc5-1.4.2/proofs/eo/cpc/` (the entire signature tree)

The verifier compares the executable bytes to the pinned ZIP, checks its version
and revision, and compares every file in the installed CPC tree with the pinned
source tarball. Missing, altered, or additional signature/helper files fail.
`signature_tree_sha256` hashes the UTF-8 concatenation of sorted
`<file SHA256><two spaces><path relative to cpc/>\n` records. The installed static
Linux x86-64 binary is cvc5 1.4.2, revision `282d5e0`.

Run commands from the repository root:

```sh
python3 -B scripts/eunoia/verify_toolchain.py \
  --toolchain-root /home/charles/code/friends/.toolchains

# All seven UF and seven LIA inputs, both option profiles; directory must be new.
python3 -B scripts/eunoia/dump_cpc.py --output /tmp/eunoia-regressions

# Selected existing regression inputs, retaining their original assertions.
python3 -B scripts/eunoia/dump_cpc.py --profile default \
  --output /tmp/eunoia-samples \
  unit-tests/files/uf4.smt2 unit-tests/files/lia1.smt2

/home/charles/code/friends/.toolchains/smtrocq-env \
  python3 -B scripts/eunoia/test_tooling.py
```

No script reads, replaces, or links `solvers/cvc5` (the separate 1.0.7 binary used
by baseline abduction tests). There is no dune or tactic integration in this
directory. The coordinator can run the last command as an independent check;
no shared dune stanza change is required for these developer tools.

`dump_cpc.py` always uses `--dump-proofs --proof-format=cpc
--proof-granularity=dsl-rewrite --no-proof-allow-trust --proof-check=eager
--check-proofs-complete`. The `default` profile keeps default preprocessing;
`reduced` adds `--simplification=none --no-static-learning --no-ite-simp
--no-unconstrained-simp --no-repeat-simp`. Detailed rewriting avoids opaque
macro steps; disabling trust asks the CPC printer to fail on missing rules.
Internal cvc5 proof checking is useful diagnostics and adds no independent
SMTCoq trust guarantee. Neither flag permits accepting the output as a theorem.

Each input must be a repository file containing exactly one QF_UF/QF_LIA query.
Input-side solver options, resets, extra queries and get-proof commands are
rejected. A capture records exact argv, input/proof/stderr hashes, toolchain pins,
source revision, and all printed rule occurrences (including `step-pop :rule
scope`). Inputs are checked for changes during each run. Nonzero exits, timeout,
SAT/unknown output, malformed or unsupported command syntax, unknown rules,
signature rules with `:sorry`, and missing explicit final `false` fail capture.
The rule names and `:sorry` markers come from the actual `Cpc.eo` include closure;
there is no manually implemented rule evaluator. No printed step is filtered out.

Results are staged in a temporary sibling directory and published only after
every requested capture succeeds. Existing output directories are preserved.
On failure the staged results are removed and the command exits 1; argument
errors exit 2. The default wall timeout is 30 seconds per run. The default
16 MiB dump size limit is checked **after** the solver exits, so it limits
retained artifacts, not temporary disk usage. Both limits are configurable.

Every report is marked `UNVERIFIED_SOLVER_OUTPUT`. The inventory parses syntax
and declaration names only: it does not evaluate CPC rules, check premise
references, validate assumption binding, or prove semantic correctness. The
signature compiler and SMTCoq/Rocq checker must still check **every** inference
and bind the exact input roots. These scripts must never become a proof
acceptance path. No Rocq lemmas or assumptions are introduced here.

See [the fixture notes](../../unit-tests/eunoia-fixtures/README.md) for measured
rule coverage and the deliberately small retained dump selection.
