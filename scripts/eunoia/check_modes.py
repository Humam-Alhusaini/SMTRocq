#!/usr/bin/env python3
"""Fresh positive/corruption replays through both native checker emitters."""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import tempfile

ROOT = Path(__file__).resolve().parents[2]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    out = args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix="eunoia-mode-replay-"))
    if out == ROOT or ROOT in out.parents:
        parser.error("replay output must be outside the checkout")
    if args.output:
        out.mkdir(parents=True, exist_ok=False)
    spec = importlib.util.spec_from_file_location("bench", ROOT / "benchmarks/eunoia/run.py")
    bench = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(bench)
    wrapper = os.environ.get("EUNOIA_ENV", str(ROOT / "scripts/eunoia/env"))
    flags = bench.rocq_loadpath(ROOT) + ["-Q", str(out), "EunoiaModeReplay"]
    compiler_flags = flags + ["-I", str(ROOT / "_build/install/default/lib")]
    summary = dict(passed=False, commands=[], sources={})
    modules = []
    try:
        for mode, disabled, forced in (("Reference", "1", "0"), ("Shared", "0", "1")):
            fixtures = [(name, ROOT / "src/eunoia_backend/tests/integration" / (name + ".v"))
                        for name in ("Proof", "Lia")]
            fixtures.append(("IntegerCasts", ROOT / "unit-tests/eunoia_integer_casts.v"))
            fixtures.append(("Division", ROOT / "unit-tests/eunoia_division.v"))
            for fixture, source in fixtures:
                name = fixture + mode
                target = out / (name + ".v")
                target.write_bytes(source.read_bytes())
                summary["sources"][name] = hashlib.sha256(target.read_bytes()).hexdigest()
                command = [wrapper, "env", "EUNOIA_DISABLE_CHECKED_CACHE=" + disabled,
                           "EUNOIA_FORCE_CHECKED_CACHE=" + forced,
                           "dune", "exec", "--", "rocq", "compile", "-q", *compiler_flags, str(target)]
                result, _ = bench.record_command(command, ROOT, 300, out / name)
                summary["commands"].append(result)
                if result["exit_code"] or result["timeout"] or not target.with_suffix(".vo").is_file():
                    raise RuntimeError(f"{name} failed; see {out / name / 'output.log'}")
                modules.append("EunoiaModeReplay." + name)
        result, _ = bench.record_command([wrapper, "rocq", "check", "-silent", *flags, *modules],
                                         ROOT, 900, out / "kernel")
        summary["commands"].append(result)
        if result["exit_code"] or result["timeout"]:
            raise RuntimeError(f"independent kernel check failed: {out / 'kernel/output.log'}")
        summary["passed"] = True
    except Exception as error:
        summary["error"] = str(error)
        raise
    finally:
        (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(f"Both checker modes passed: {out}")


if __name__ == "__main__":
    main()
