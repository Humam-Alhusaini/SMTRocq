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
    parser.add_argument("--modes", nargs="+", choices=("Reference", "Shared", "Helpers", "Conclusions", "Indexed", "Staged", "Direct", "DirectShared", "DirectReference", "IndexedAdaptive", "IndexedReference", "Specialized", "SpecializedShared", "SpecializedReference", "Model", "ModelShared", "ModelReference", "Certificates", "CertificatesShared", "CertificatesModel"),
                        default=("Reference", "Shared", "Helpers", "Conclusions", "Indexed", "Staged", "Direct", "Specialized"))
    parser.add_argument("--fixtures", nargs="+",
                        choices=("Proof", "Lia", "IntegerCasts", "Division",
                                 "Uf", "UfBool", "Purification", "PublicLia", "PublicTactics"))
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
    summary = dict(passed=False, commands=[], sources={},
                   single_kernel_acceptance=os.environ.get("EUNOIA_SINGLE_KERNEL_ACCEPTANCE", "1"),
                   trace_constants=os.environ.get("EUNOIA_TRACE_CONSTANTS", "1"))
    modules = []
    try:
        for mode, disabled, forced, helpers, conclusions, indexed, direct in (
                ("Reference", "1", "0", "0", "0", "0", "0"),
                ("Shared", "0", "1", "0", "0", "0", "0"),
                ("Helpers", "0", "1", "1", "0", "0", "0"),
                ("Conclusions", "0", "1", "0", "1", "0", "0"),
                ("Indexed", "0", "1", "0", "1", "1", "0"),
                ("Staged", "0", "1", "0", "1", "0", "0"),
                ("Direct", "0", "0", "0", "1", "0", "1"),
                ("DirectShared", "0", "1", "0", "1", "0", "1"),
                ("DirectReference", "1", "0", "0", "1", "0", "1"),
                ("IndexedAdaptive", "0", "0", "0", "1", "1", "0"),
                ("IndexedReference", "1", "0", "0", "1", "1", "0"),
                ("Specialized", "0", "0", "0", "1", "0", "0"),
                ("SpecializedShared", "0", "1", "0", "1", "0", "0"),
                ("SpecializedReference", "1", "0", "0", "1", "0", "0"),
                ("Model", "0", "0", "0", "0", "0", "0"),
                ("ModelShared", "0", "1", "0", "0", "0", "0"),
                ("ModelReference", "1", "0", "0", "0", "0", "0"),
                ("Certificates", "0", "0", "0", "0", "0", "0"),
                ("CertificatesShared", "0", "1", "0", "0", "0", "0"),
                ("CertificatesModel", "0", "0", "0", "0", "0", "0")):
            if mode not in args.modes:
                continue
            fixtures = [(name, ROOT / "src/eunoia_backend/tests/integration" / (name + ".v"))
                        for name in ("Proof", "Lia")]
            fixtures.append(("IntegerCasts", ROOT / "unit-tests/eunoia_integer_casts.v"))
            fixtures.append(("Division", ROOT / "unit-tests/eunoia_division.v"))
            if mode.startswith(("Model", "Certificates")) or mode in ("Conclusions", "Indexed", "Staged", "Direct", "IndexedAdaptive", "IndexedReference", "Specialized"):
                fixtures += [(name, ROOT / "unit-tests" / (source + ".v")) for name, source in
                             (("Uf", "eunoia_uf"), ("UfBool", "eunoia_uf_bool"),
                              ("Purification", "eunoia_purification"), ("PublicLia", "eunoia_lia"),
                              ("PublicTactics", "eunoia_tactics"))]
            if args.fixtures:
                available = {name for name, _ in fixtures}
                if not set(args.fixtures) <= available:
                    parser.error("a selected fixture is unavailable in mode " + mode)
                fixtures = [(name, source) for name, source in fixtures if name in args.fixtures]
            for fixture, source in fixtures:
                name = fixture + mode
                target = out / (name + ".v")
                target.write_bytes(source.read_bytes())
                summary["sources"][name] = hashlib.sha256(target.read_bytes()).hexdigest()
                command = [wrapper, "env",
                           "EUNOIA_MODEL_DAG=" + ("1" if mode.startswith("Model") or mode == "CertificatesModel" else "0"), "EUNOIA_DISABLE_CHECKED_CACHE=" + disabled,
                           "EUNOIA_FORCE_CHECKED_CACHE=" + forced,
                           "EUNOIA_DIRECT_CERTIFICATES=" + ("1" if mode.startswith("Certificates") else "0"), "EUNOIA_HELPER_CACHE=" + helpers,
                           "EUNOIA_DIRECT_PROGRAMS=" + direct,
                           "EUNOIA_SPECIALIZED_RULES=" + ("1" if mode.startswith("Specialized") else "0"),
                           "EUNOIA_STAGED_PROGRAMS=" + ("1" if mode == "Staged" else "0"),
                           "EUNOIA_DECLARED_CONCLUSIONS=" + conclusions, "EUNOIA_PROGRAM_INDEX=" + indexed,
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
    print(f"Checker modes {', '.join(args.modes)} passed: {out}")


if __name__ == "__main__":
    main()
