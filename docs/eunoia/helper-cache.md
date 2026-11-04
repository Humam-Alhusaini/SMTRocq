# Checked sharing of Eunoia helper computations

`EUNOIA_HELPER_CACHE=1` enables an experimental producer and checker path.
It is disabled by default pending end-to-end measurements. It is separate
from the existing cache of local SMTCoq certificates.

The interpreter caches generated helper calls, rather than rule names or
inference results. A key contains the exact helper name, argument terms and
call depth. Depth identifies the remaining fuel under the fixed evaluation
budget; a hit cannot bypass a fuel failure. Type queries, nil resolution,
primitive hooks and generated programs are fixed while a cache is used.

Every proposed entry is checked, including unused entries. Validation runs
from the tail of the hint list and may use only already validated entries.
The cache cannot justify itself or a mutually recursive cycle. The generic
`evaluate_cached_refinement` theorem proves equality with the complete
reference computation, including failure results. The rule and surface
wrappers extend that result to generated CPC derivation.

`EunoiaHelperCache.checker_refinement` proves that acceptance implies acceptance
by the existing `EunoiaMemo` checker. Every source step is still evaluated;
ordered premise binding, result binding, scoped discharge and the local
semantic gate remain mandatory. Closing scope rules currently use the
reference evaluator. Incorrect candidate collection cannot establish a proof.

The producer is untrusted. It observes generated helper evaluations, selects
repeated calls, and emits at most 128 entries from a pool of 4,096 keys.
Collection retains at most 256 entries per source-rule request. The heuristics
use syntax size and repetition only; they do not whitelist helper or rule
names. Rocq validates the selected entries under the final checker context.

A preliminary repeated-rule component measurement included cache validation,
surface conversion and `Qed`: 3,000 evaluations of `arith_poly_norm` took
3.485 seconds with the reference evaluator and 2.347 seconds with sharing
(`Qed`: 3.472 and 2.484 seconds). Candidate collection was performed before
that component timer. This is not an end-to-end tactic benchmark or an
external-prover comparison; production enablement requires matched full
proof measurements including collection and kernel checking.

To reproduce the component diagnostic with a configured toolchain:

```sh
EUNOIA_KEEP_TEST_DIR=1 bash tools/eunoia/check-generated.sh
# Set artifact_dir to the retained directory printed by that command.
cp tools/eunoia/tests/HelperMemoBench.v "$artifact_dir/"
(cd "$artifact_dir" && rocq compile -q -Q . SMTCoq.checker.eunoia HelperMemoBench.v)
(cd "$artifact_dir" && rocq check -silent -Q . SMTCoq.checker.eunoia SMTCoq.checker.eunoia.HelperMemoBench)
```

For complete tactic measurements, use `benchmarks/eunoia/run.py` on a frozen
revision, alternate `EUNOIA_HELPER_CACHE=0` and `=1`, and keep identical cases,
timeouts, compiler and artifacts. The harness records the switch in metadata.
