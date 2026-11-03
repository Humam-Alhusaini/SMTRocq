#!/usr/bin/env python3
"""Focused checked-certificate probe, with all helper work inside Time tactic.

Uses the existing developer profiler's loadpaths and profile parser. This does
not alter the benchmark harness, solver limits, fuel, or production checker.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("eunoia_profile", ROOT / "tools/eunoia-profile/run.py")
profile = importlib.util.module_from_spec(spec)
spec.loader.exec_module(profile)
audit_spec = importlib.util.spec_from_file_location("eunoia_audit", ROOT / "tools/audit-eunoia-assumptions.py")
auditor = importlib.util.module_from_spec(audit_spec)
audit_spec.loader.exec_module(auditor)
WRAPPER = profile.WRAPPER
CASES = {
    "congruence": profile.CASES["congruence"],
    "predicate": profile.CASES["predicate"],
    "negative_predicate": (
        "forall (A : Type) (HA : CompDec A) (p : A -> bool) (x y : A), "
        "x = y -> p x = false -> p y = false", "cvc5_eunoia"),
    "two_sorts": (
        "forall (A B : Type) (HA : CompDec A) (HB : CompDec B) "
        "(f : A -> B) (g : B -> A) (x y : A), x = y -> g (f x) = g (f y)", "cvc5_eunoia"),
    "supplied": (
        "forall (A : Type) (HA : CompDec A) (f : A -> A) (x y z : A) "
        "(Hxy : x = y) (Hyz : y = z), f x = f z",
        "intros; cvc5_eunoia (Hxy, Hyz, Hxy)"),
    "lia": ("forall x : Z, x <= 0 -> x >= 1 -> False", "cvc5_eunoia"),
    "lia_replay": profile.CASES["arithmetic_replay"],
    "scoped_lia": ("forall x : Z, implb (x >=? 0) (-2*x <=? -2*0) = true", "backend_lia_scoped"),
    "nested_scope": ("forall p q : bool, implb p (implb q p) = true", "backend_scope_required_nested"),
}
DEFAULT_CASES = list(CASES)
# Exact theorem from the parent's completed 604c043 diagnostic; opt-in only.
CASES["integer_transitive"] = (
    "forall (x y z : Z) (f : Z -> Z), (x =? y) && (y =? z) && negb (f x =? f z) = false",
    "cvc5_eunoia")
CONTROL_THEOREMS = ("failed_certificate_rollback", "source_mutations", "witness_mutations",
                    "scope_bindings", "missing_intermediate_instance", "false_controls",
                    "undo_checked_certificate", "section_carriers")
CONTROL_HELPERS = tuple(name for name in CONTROL_THEOREMS
                        if name not in ("missing_intermediate_instance", "false_controls"))


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def execute(command, directory, timeout):
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    start = time.perf_counter()
    with (directory / "output.log").open("w") as log:
        process = subprocess.Popen(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT,
                                   start_new_session=True)
        timed_out = False
        try:
            process.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
        except BaseException:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
            raise
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    result = dict(command=command, cwd=str(ROOT), exit_code=process.returncode,
                  timeout=timed_out, process_wall_s=time.perf_counter() - start,
                  process_user_s=after.ru_utime - before.ru_utime,
                  process_system_s=after.ru_stime - before.ru_stime)
    profile.write_json(directory / "command.json", result)
    return result


def audit_helpers(directory, module, theorems, flags, timeout):
    """Audit saved bodies, including helpers inlined by the supported Qed API."""
    directory.mkdir()
    source = directory / "Helpers.v"
    source.write_text(f"Require {module}.\n" + "\n".join(
        f'Redirect "{directory / name}" Eunoia_helper_assumptions "{module}.{name}".'
        for name in theorems) + "\n")
    result = execute([WRAPPER, "dune", "exec", "-j2", "--", "rocq", "c", "-q", *flags,
                      "-I", str(ROOT / "_build/install/default/lib"), str(source)], directory, timeout)
    failed = bool(result["exit_code"]) or result["timeout"]
    baseline = {line.strip() for line in (ROOT / "docs/eunoia/baseline-assumptions.txt").read_text().splitlines()
                if line.strip() and not line.startswith("#")}
    reports = []
    if not failed:
        for name in theorems:
            entry = dict(theorem=name)
            try:
                dependencies = auditor.assumptions((directory / (name + ".out")).read_text())
                entry.update(assumptions=sorted(dependencies), new_assumptions=sorted(dependencies - baseline))
                failed |= bool(dependencies - baseline)
            except (OSError, ValueError) as error:
                entry["error"] = str(error)
                failed = True
            reports.append(entry)
    profile.write_json(directory / "summary.json", dict(passed=not failed, command=result, helpers=reports))
    return int(failed)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--cases", nargs="+", choices=CASES, default=DEFAULT_CASES)
    parser.add_argument("--repeat", type=int, default=1)
    parser.add_argument("--timeout", type=float, default=120)
    parser.add_argument("--helpers", action="store_true", help="audit actual saved checker certificate bodies")
    parser.add_argument("--kernel-check", action="store_true")
    parser.add_argument("--controls", action="store_true")
    args = parser.parse_args()
    output = args.output.resolve()
    if output == ROOT or ROOT in output.parents or '"' in str(output) or "\n" in str(output):
        parser.error("output must be external and contain no quotes or newlines")
    if args.repeat <= 0 or args.timeout <= 0:
        parser.error("repeat and timeout must be positive")
    output.mkdir(parents=True, exist_ok=False)
    builddir = output / "build"
    builddir.mkdir()
    build = execute([WRAPPER, "dune", "build", "-j2",
                     "src/smtcoq.cmxs",
                     "src/eunoia_backend/eunoia_backend.cmxs",
                     "src/eunoia_backend/tests/integration/backend_test_plugin.cmxs"], builddir, args.timeout)
    if build["exit_code"] or build["timeout"]:
        return 1
    metadata = dict(argv=os.sys.argv, root=str(ROOT), fuel=10000, cases=CASES,
                    loadavg_start=os.getloadavg(), source_sha256={}, artifact_sha256={},
                    profile_components=os.environ.get("ROCQ_PROFILE_COMPONENTS", "default"))
    for cmd in (["git", "rev-parse", "HEAD"], ["git", "branch", "--show-current"],
                ["git", "diff"], [WRAPPER, "rocq", "c", "--version"]):
        metadata[" ".join(cmd)] = subprocess.run(cmd, cwd=ROOT, text=True,
                                                 capture_output=True, check=True).stdout
    for base, field in ((ROOT, "source_sha256"), (ROOT / "_build/default", "artifact_sha256")):
        # Explicit paths avoid depending on the caller's working directory.
        if base == ROOT:
            paths = [Path(p) for p in (
                "src/eunoia_backend/eunoiaBackend.ml", "src/eunoia_backend/eunoiaBackend.mli",
                "src/eunoia_backend/eunoiaRocq.ml", "src/eunoia_backend/eunoiaSolver.ml",
                "src/eunoia_backend/tests/integration/g_backend_test.mlg",
                "tools/eunoia-proof-reuse/run.py", "tools/eunoia-proof-reuse/Controls.v",
                "tools/eunoia-profile/run.py", "docs/eunoia/baseline-assumptions.txt")]
            paths += [p.relative_to(ROOT) for p in (ROOT / "theories/checker/eunoia").glob("*.v")]
        else:
            paths = [Path("src/smtcoq.cmxs"), Path("src/eunoia_backend/eunoia_backend.cmxs"),
                     Path("src/eunoia_backend/tests/integration/backend_test_plugin.cmxs")]
            paths += [p.relative_to(base) for p in (base / "theories").rglob("*.vo")]
        metadata[field] = {str(p): digest(base / p) for p in sorted(paths)}
    profile.write_json(output / "metadata.json", metadata)
    for relative in metadata["source_sha256"]:
        snapshot = output / "sources" / relative
        snapshot.parent.mkdir(parents=True, exist_ok=True)
        snapshot.write_bytes((ROOT / relative).read_bytes())
    rows = []
    failed = False
    for repetition in range(1, args.repeat + 1):
        for name in args.cases:
            directory = output / f"{name}-{repetition}"
            directory.mkdir()
            statement, tactic = CASES[name]
            source = profile.source(statement, tactic, directory)
            (directory / "Case.v").write_text(source)
            flags = [*profile.loadpath(), "-Q", str(directory), "EunoiaProofReuse"]
            row = dict(case=name, repeat=repetition, **execute(
                [WRAPPER, "dune", "exec", "-j2", "--", "rocq", "c", "-q", "-color", "no",
                 *flags, "-I", str(ROOT / "_build/install/default/lib"), str(directory / "Case.v")],
                directory, args.timeout))
            log = (directory / "output.log").read_text()
            timings = profile.TIMING.findall(log)
            row["checked"] = (row["exit_code"] == 0 and not row["timeout"] and len(timings) == 2
                              and (directory / "Case.vo").is_file() and "EUNOIA_PROFILE_CHECKED" in log)
            if row["checked"]:
                for stage, timing in zip(("tactic", "qed"), timings):
                    row[f"{stage}_wall_s"], row[f"{stage}_user_s"], row[f"{stage}_system_s"] = map(float, timing)
                    row[f"{stage}_profile"] = profile.trace_summary(directory / f"{stage}.json")
                auditdir = directory / "audit"
                auditdir.mkdir()
                command = ["python3", "-B", str(ROOT / "tools/audit-eunoia-assumptions.py"),
                           "--import", "EunoiaProofReuse.Case", "--theorem", "profile_result",
                           "--loadpath", str(directory), "EunoiaProofReuse", "--output-dir", str(auditdir)]
                audit = execute(command, auditdir, args.timeout)
                row["audit_exit_code"] = audit["exit_code"]
                failed |= bool(audit["exit_code"]) or audit["timeout"]
                if args.helpers:
                    row["helper_audit_exit_code"] = audit_helpers(
                        directory / "helpers", "EunoiaProofReuse.Case", ["profile_result"], flags, args.timeout)
                    failed |= bool(row["helper_audit_exit_code"])
                if args.kernel_check:
                    kerneldir = directory / "kernel"
                    kerneldir.mkdir()
                    check = execute([WRAPPER, "rocq", "check", "-silent", "-bytecode-compiler", "yes",
                                     *flags, "EunoiaProofReuse.Case"], kerneldir, args.timeout)
                    row["kernel_exit_code"] = check["exit_code"]
                    failed |= bool(check["exit_code"]) or check["timeout"]
            failed |= not row["checked"]
            rows.append(row)
            profile.write_json(output / "results.json", rows)
            print(f"{name} {repetition}: checked={row['checked']}, exit={row['exit_code']}, "
                  f"tactic={row.get('tactic_wall_s')}, Qed={row.get('qed_wall_s')}", flush=True)
    if args.controls:
        directory = output / "controls"
        directory.mkdir()
        (directory / "Controls.v").write_bytes(Path(__file__).with_name("Controls.v").read_bytes())
        flags = [*profile.loadpath(), "-Q", str(directory), "EunoiaProofReuseControls"]
        result = execute([WRAPPER, "dune", "exec", "-j2", "--", "rocq", "c", "-q", *flags,
                          "-I", str(ROOT / "_build/install/default/lib"), str(directory / "Controls.v")],
                         directory, args.timeout)
        failed |= bool(result["exit_code"]) or result["timeout"]
        if not result["exit_code"] and not result["timeout"]:
            auditdir = directory / "audit"
            auditdir.mkdir()
            command = ["python3", "-B", str(ROOT / "tools/audit-eunoia-assumptions.py"),
                       "--import", "EunoiaProofReuseControls.Controls", "--loadpath", str(directory),
                       "EunoiaProofReuseControls", "--output-dir", str(auditdir)]
            for name in CONTROL_THEOREMS:
                command += ["--theorem", name]
            audit = execute(command, auditdir, args.timeout)
            failed |= bool(audit["exit_code"]) or audit["timeout"]
            if args.helpers:
                failed |= bool(audit_helpers(directory / "helpers", "EunoiaProofReuseControls.Controls",
                                             CONTROL_HELPERS, flags, args.timeout))
            if args.kernel_check:
                kerneldir = directory / "kernel"
                kerneldir.mkdir()
                check = execute([WRAPPER, "rocq", "check", "-silent", "-bytecode-compiler", "yes",
                                 *flags, "EunoiaProofReuseControls.Controls"], kerneldir, args.timeout)
                failed |= bool(check["exit_code"]) or check["timeout"]
        print(f"controls: exit={result['exit_code']}", flush=True)
    metadata["loadavg_end"] = os.getloadavg()
    metadata["artifact_sha256_end"] = {p: digest(ROOT / "_build/default" / p)
                                       for p in metadata["artifact_sha256"]}
    failed |= metadata["artifact_sha256"] != metadata["artifact_sha256_end"]
    profile.write_json(output / "metadata.json", metadata)
    profile.write_json(output / "status.json", dict(passed=not failed))
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
