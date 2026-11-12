#!/usr/bin/env python3
"""Matching live public-goal profiles using the existing checked profile driver.

All fuel, solver, capacity and callback choices remain production defaults.
Raw Time tactic/Qed CPU and wall rows are in each output.log. Inclusive native
profile events overlap: never sum them as a decomposition of elapsed time.
"""
import hashlib
import importlib.util
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("eunoia_profile", ROOT / "tools/eunoia-profile/run.py")
profile = importlib.util.module_from_spec(spec)
spec.loader.exec_module(profile)
profile.CASES = {
    "congruence": profile.CASES["congruence"],
    "predicate": profile.CASES["predicate"],
    "lia_bounds": ("forall x : Z, x <= 0 -> x >= 1 -> False", "cvc5_eunoia"),
    "lia_normalization": ("forall x y : Z, 2*(x+y) = 2*x + 2*y", "cvc5_eunoia"),
    "lia_scoped": ("forall x : Z, Bool.eqb (x <=? 0) (negb (x >? 0)) = true", "cvc5_eunoia"),
}
SOURCES = ["theories/checker/eunoia/" + name + ".v" for name in
           ("EoRuntime", "CpcGenerated", "EunoiaAdapter", "EunoiaLocal", "EunoiaTactic",
            "EunoiaScopedAdapter", "EunoiaChecker", "EunoiaScope")]
SOURCES += ["tools/eunoia-context-profile/run.py", "tools/eunoia-context-profile/summarize.py"]


def snapshot():
    return {"head": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
            "diff": subprocess.check_output(["git", "diff"], cwd=ROOT, text=True),
            "sha256": {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in SOURCES}}


if __name__ == "__main__":
    before = snapshot()
    result = profile.main()
    if "--output" in sys.argv:
        output = Path(sys.argv[sys.argv.index("--output") + 1])
        if output.is_dir():
            after = snapshot()
            (output / "context-metadata.json").write_text(json.dumps(
                {"before": before, "after": after, "sources_unchanged": before == after}, indent=2) + "\n")
            if before != after:
                raise RuntimeError("measured sources changed during the profile")
    raise SystemExit(result)
