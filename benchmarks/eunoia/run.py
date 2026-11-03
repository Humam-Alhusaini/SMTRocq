#!/usr/bin/env python3
"""Measure checked SMTCoq tactics; retain all commands, proofs, and diagnostics."""

import argparse
from collections import Counter
import csv
import ctypes
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import math
import os
from pathlib import Path
import platform
import re
import signal
import statistics
import subprocess
import sys
import tempfile
import time


HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
WRAPPER = Path("/home/charles/code/friends/.toolchains/smtrocq-env")
BACKENDS = {name: name for name in ("verit", "cvc4", "cvc5_eunoia")}
BASELINE_PATH = REPO / "docs/eunoia/baseline-assumptions.txt"
BASELINE = {line.strip() for line in BASELINE_PATH.read_text().splitlines()
            if line.strip() and not line.startswith("#")}
_audit_spec = importlib.util.spec_from_file_location(
    "eunoia_assumption_audit", REPO / "tools/audit-eunoia-assumptions.py")
_audit = importlib.util.module_from_spec(_audit_spec)
_audit_spec.loader.exec_module(_audit)
if not BASELINE or any(not _audit.IDENT.fullmatch(name) for name in BASELINE):
    raise ValueError("Invalid checker assumption baseline")
BEGIN = "EUNOIA_BENCH_TACTIC_BEGIN"
END = "EUNOIA_BENCH_TACTIC_END"
ASSUMPTIONS = "EUNOIA_BENCH_ASSUMPTIONS"
DONE = "EUNOIA_BENCH_CHECKED"
TIMING = re.compile(r"(?:Finished|Completed)(?: (?:failing|successfully))? transaction in "
                    r"([0-9.]+) secs? \(([0-9.]+)u,([0-9.]+)s\)")

# Some Python distributions omit these Linux APIs even when libc has them.
PIDFD_LIBC = None
if sys.platform == "linux" and not (hasattr(os, "pidfd_open") and
                                       hasattr(signal, "pidfd_send_signal")):
    candidate = ctypes.CDLL(None, use_errno=True)
    if hasattr(candidate, "pidfd_open") and hasattr(candidate, "pidfd_send_signal"):
        candidate.pidfd_open.argtypes = [ctypes.c_int, ctypes.c_uint]
        candidate.pidfd_send_signal.argtypes = [ctypes.c_int, ctypes.c_int,
                                                ctypes.c_void_p, ctypes.c_uint]
        candidate.pidfd_open.restype = candidate.pidfd_send_signal.restype = ctypes.c_int
        PIDFD_LIBC = candidate


def pidfd_call(name, *arguments):
    if PIDFD_LIBC is None:
        api = os.pidfd_open if name == "pidfd_open" else signal.pidfd_send_signal
        return api(*arguments)
    arguments = arguments + ((0,) if name == "pidfd_open" else (None, 0))
    result = getattr(PIDFD_LIBC, name)(*arguments)
    if result < 0:
        error = ctypes.get_errno()
        raise OSError(error, os.strerror(error))
    return result


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def process_identity(pid):
    """Read Linux parent/start identifiers without assuming a simple comm field."""
    try:
        fields = Path(f"/proc/{pid}/stat").read_text().rsplit(")", 1)[1].split()
        return int(fields[1]), int(fields[19])
    except (OSError, ValueError, IndexError):
        return None


def kill_process_tree(proc):
    # cvc5 deliberately calls setsid, escaping the compiler's process group.
    # Pin each observed descendant with a pidfd before killing the compiler;
    # checking its start identifier avoids signalling a reused numeric PID.
    handles = []
    if PIDFD_LIBC is not None or (hasattr(os, "pidfd_open") and
                                   hasattr(signal, "pidfd_send_signal")):
        snapshot = {int(p.name): identity for p in Path("/proc").glob("[0-9]*")
                    if (identity := process_identity(p.name)) is not None}
        descendants = {proc.pid}
        pending = set(snapshot) - descendants
        while True:
            children = {pid for pid in pending if snapshot[pid][0] in descendants}
            if not children:
                break
            descendants.update(children)
            pending.difference_update(children)
        for pid in descendants - {proc.pid}:
            try:
                handle = pidfd_call("pidfd_open", pid)
            except ProcessLookupError:
                continue
            if process_identity(pid) == snapshot[pid]:
                handles.append(handle)
            else:
                os.close(handle)
    try:
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        for handle in handles:
            try:
                pidfd_call("pidfd_send_signal", handle, signal.SIGKILL)
            except ProcessLookupError:
                pass
    finally:
        for handle in handles:
            os.close(handle)


def execute(command, cwd, timeout):
    """Kill the compiler group and observed Linux descendants on timeout."""
    start = time.perf_counter()
    try:
        proc = subprocess.Popen(command, cwd=cwd, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True,
                                start_new_session=True)
    except OSError as exc:
        return {"command": command, "cwd": str(cwd), "exit_code": None,
                "timeout": False, "launch_error": str(exc), "output": str(exc),
                "process_wall_s": time.perf_counter() - start}
    timed_out = False
    try:
        output, _ = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        timed_out = True
        kill_process_tree(proc)
        output, _ = proc.communicate()
    except BaseException:
        kill_process_tree(proc)
        proc.communicate()
        raise
    return {"command": command, "cwd": str(cwd), "exit_code": proc.returncode,
            "timeout": timed_out, "output": output,
            "process_wall_s": time.perf_counter() - start}


def record_command(command, cwd, timeout, directory):
    result = execute(command, cwd, timeout)
    directory.mkdir(parents=True, exist_ok=True)
    (directory / "output.log").write_text(result.pop("output"))
    write_json(directory / "command.json", result)
    return result, (directory / "output.log").read_text()


def load_cases(path):
    cases = json.loads(path.read_text())
    ids = set()
    for case in cases:
        if not re.fullmatch(r"[a-z][a-z0-9_]*", case["id"]) or case["id"] in ids:
            raise ValueError("Case identifiers must be unique lowercase identifiers")
        ids.add(case["id"])
        if case["theory"] not in ("UF", "LIA") or case["expected"] not in ("proved", "rejected"):
            raise ValueError("Invalid case theory or expectation")
        # Fixtures contain only a theorem statement, never vernacular commands.
        if '"' in case["statement"] or re.search(r"\.(?![A-Za-z_])", case["statement"]):
            raise ValueError("Use a theorem statement without vernacular terminators")
    return cases


def prelude(extra_imports, scoped=False):
    if scoped:
        modules = ["SMTCoq.SMTCoq", "Stdlib.Bool.Bool", "Stdlib.ZArith.ZArith", *extra_imports]
        return ("".join(f"Require {name}.\n" for name in modules)
                + "Module EunoiaBenchmark.\n"
                + "".join(f"Import {name}.\n" for name in modules)
                + "Local Open Scope Z_scope.\n")
    return ("From SMTCoq Require Import SMTCoq.\n"
            "From Stdlib Require Import Bool ZArith.\n"
            + "".join(f"Require Import {name}.\n" for name in extra_imports)
            + "Local Open Scope Z_scope.\n")


def source(case, backend, extra_imports):
    # A negative case is deliberately attempted as a real proof. Its failed
    # compilation is retained; there is no discarded or unfinished proof file
    # that can successfully compile and accidentally enter the solved count.
    return (prelude(extra_imports, scoped=True)
            + f"Lemma bench_result : {case['statement']}.\nProof.\n"
            + f'  idtac "{BEGIN}".\n  Time {BACKENDS[backend]}.\n'
            + "Time Qed.\n"
            + "End EunoiaBenchmark.\n"
            + f'Goal True. Proof. idtac "{END}" "{ASSUMPTIONS}". exact I. Qed.\n'
            + "Print Assumptions EunoiaBenchmark.bench_result.\n"
            + f'Goal True. Proof. idtac "{DONE}". exact I. Qed.\n')


def classify(case, execution, output, vo_exists):
    row = {"status": "error", "solved": False, "tactic_wall_s": None,
           "qed_wall_s": None, "tactic_user_s": None, "tactic_system_s": None,
           "assumptions": None, "new_assumptions": None}
    timings = TIMING.findall(output.split(BEGIN, 1)[1].split(END, 1)[0]) if BEGIN in output else []
    if timings:
        row.update(tactic_wall_s=float(timings[0][0]), tactic_user_s=float(timings[0][1]),
                   tactic_system_s=float(timings[0][2]))
    if execution["timeout"]:
        row["status"] = "timeout"
        return row
    if execution["exit_code"] != 0:
        # A parser/import failure before the tactic is an infrastructure error.
        if case["expected"] == "rejected" and BEGIN in output and END not in output:
            row["status"] = "negative_rejected"
        return row
    if DONE not in output or not vo_exists:
        return row
    if case["expected"] == "rejected":
        row["status"] = "negative_unexpected_success"
        return row
    if BEGIN not in output or END not in output or ASSUMPTIONS not in output:
        return row
    if len(timings) != 2:
        row["status"] = "timing_error"
        return row
    try:
        names = _audit.assumptions(output.split(ASSUMPTIONS, 1)[1].split(DONE, 1)[0])
    except ValueError:
        row["status"] = "assumption_error"
        return row
    row["assumptions"] = sorted(names)
    row["new_assumptions"] = sorted(names - BASELINE)
    if row["new_assumptions"]:
        row["status"] = "unsupported_assumptions"
        return row
    row.update(status="solved", solved=True, tactic_wall_s=float(timings[0][0]),
               tactic_user_s=float(timings[0][1]), tactic_system_s=float(timings[0][2]),
               qed_wall_s=float(timings[1][0]))
    return row


def summarize(rows):
    summary = {}
    for backend in sorted({r["backend"] for r in rows}):
        subset = [r for r in rows if r["backend"] == backend]
        positive = [r for r in subset if r["expected"] == "proved"]
        solved = [r for r in positive if r["solved"]]
        case_ids = {r["case_id"] for r in positive}
        all_runs = [c for c in case_ids
                    if all(r["solved"] for r in positive if r["case_id"] == c)]
        times = [r["tactic_wall_s"] for r in solved]
        summary[backend] = {
            "positive_cases": len(case_ids), "positive_scheduled": len(positive),
            "positive_attempts": sum(r["status"] != "unavailable" for r in positive),
            "solved_attempts": len(solved), "cases_solved_every_repeat": len(all_runs),
            "status_counts": dict(Counter(r["status"] for r in subset)),
            "solved_tactic_wall_sum_s": sum(times) if times else None,
            "solved_tactic_wall_median_s": statistics.median(times) if times else None,
            "solved_qed_wall_sum_s": sum(r["qed_wall_s"] for r in solved) if solved else None,
            "positive_process_wall_sum_s": (sum(r["process_wall_s"] or 0 for r in positive)
                                            if any(r["process_wall_s"] is not None for r in positive) else None),
            "per_theory": {
                theory: {"positive_scheduled": sum(r["theory"] == theory for r in positive),
                         "positive_attempts": sum(r["theory"] == theory and r["status"] != "unavailable"
                                                  for r in positive),
                         "solved_attempts": sum(r["theory"] == theory for r in solved)}
                for theory in ("UF", "LIA")},
        }
    return summary


def rocq_loadpath(repo):
    # Derive the actual logical names, including small-checkers/small_checker,
    # from existing stanzas, without changing any Dune files.
    flags = []
    for dune in sorted((repo / "theories").rglob("dune"), key=lambda p: (len(p.parts), str(p))):
        match = re.search(r"\(name\s+(SMTCoq(?:\.[A-Za-z0-9_]+)*)\)", dune.read_text())
        if match:
            physical = repo / "_build/default" / dune.parent.relative_to(repo)
            flags.extend(["-Q", str(physical), match[1]])
    return flags


def parse_args():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wrapper", type=Path, default=WRAPPER)
    parser.add_argument("--cases", type=Path, default=HERE / "cases.json",
                        help="JSON workload manifest; its exact contents are retained")
    parser.add_argument("--backends", nargs="+", choices=BACKENDS, default=["verit", "cvc4"])
    parser.add_argument("--repeat", type=int, default=3)
    parser.add_argument("--timeout", type=float, default=30, help="seconds per compiler process")
    parser.add_argument("--build-timeout", type=float, default=900)
    parser.add_argument("--jobs", type=int, default=2, help="Dune build concurrency (cases run serially)")
    parser.add_argument("--output", type=Path, help="new results directory; default outside the repository in /tmp")
    parser.add_argument("--skip-build", action="store_true", help="use an already successful dune build theories")
    parser.add_argument("--extra-import", action="append", default=[], metavar="ROCQ.MODULE")
    args = parser.parse_args()
    for name in args.extra_import:
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*", name):
            parser.error("Invalid Rocq module name")
    if args.repeat < 1 or args.jobs < 1 or any(not math.isfinite(t) or t <= 0
                                             for t in (args.timeout, args.build_timeout)):
        parser.error("Repeats, jobs, and finite timeouts must be positive")
    args.backends = list(dict.fromkeys(args.backends))
    return args


def main():
    args = parse_args()
    wrapper = args.wrapper.resolve()
    output = (args.output.resolve() if args.output else
              Path(tempfile.mkdtemp(prefix="smtrocq-eunoia-", dir="/tmp")))
    if args.output:
        output.mkdir(parents=True, exist_ok=False)
    print(f"Results: {output}", flush=True)
    cases_path = args.cases.resolve()
    cases = load_cases(cases_path)
    write_json(output / "cases.json", cases)
    metadata = {
        "schema_version": 1, "started_utc": datetime.now(timezone.utc).isoformat(),
        "repository": str(REPO), "wrapper": str(wrapper), "wrapper_sha256": sha256(wrapper),
        "argv": sys.argv, "python": sys.version, "platform": platform.platform(),
        "configuration": vars(args) | {"wrapper": str(wrapper), "output": str(output),
                                       "cases": str(cases_path)},
        "cases_sha256": sha256(cases_path),
        "assumption_baseline_sha256": sha256(BASELINE_PATH),
        "assumption_audit_sha256": sha256(REPO / "tools/audit-eunoia-assumptions.py"),
        "source_sha256": {p.name: sha256(p) for p in HERE.iterdir() if p.is_file()},
        "measurements": "Rocq Time backend, Time Qed, and separate compiler process wall time; no solver-only timings",
        "tools": {},
    }
    probes = {
        "git_head": ["git", "rev-parse", "HEAD"],
        "git_branch": ["git", "branch", "--show-current"],
        "git_status": ["git", "status", "--porcelain"],
        "git_diff": ["git", "diff", "--", "benchmarks/eunoia"],
        "rocq": [str(wrapper), "rocq", "--version"],
        "ocaml": [str(wrapper), "ocamlc", "-version"],
        "dune": [str(wrapper), "dune", "--version"],
        "verit": [str(wrapper), "veriT", "--version"],
        "cvc4": [str(wrapper), "cvc4", "--version"],
        "cvc5": [str(wrapper), "cvc5", "--version"],
        "paths": [str(wrapper), "python3", "-c",
                  "import json, os, shutil; print(json.dumps({'executables': "
                  "{n: shutil.which(n) for n in ['rocq','ocamlc','dune','veriT','cvc4','cvc5','lean','lake','isabelle']}, "
                  "'environment': {n: os.getenv(n) for n in ['PATH','OPAMROOT','OPAM_SWITCH_PREFIX','LFSCSIGS']}}))"],
    }
    if "cvc5_eunoia" in args.backends:
        # The new backend uses its pinned private executable, independently of
        # the older cvc5 retained on PATH for the existing abduction backend.
        probes["cvc5_eunoia_toolchain"] = [str(wrapper), "python3", "-B",
            str(REPO / "scripts/eunoia/verify_toolchain.py")]
        backend_source = REPO / "src/eunoia_backend/eunoiaSolver.ml"
        metadata["eunoia_solver_source_sha256"] = sha256(backend_source)
    for name, command in probes.items():
        result, diagnostic = record_command(command, REPO, 30, output / "metadata" / name)
        metadata["tools"][name] = result | {"output": diagnostic}
    paths = metadata["tools"]["paths"]
    if paths["exit_code"] == 0:
        binaries = json.loads(paths["output"])["executables"]
        metadata["executable_sha256"] = {n: sha256(Path(p)) for n, p in binaries.items()
                                          if p and Path(p).is_file()}
    write_json(output / "metadata.json", metadata)
    private = metadata["tools"].get("cvc5_eunoia_toolchain")
    if private and (private["exit_code"] != 0 or private["timeout"]):
        print("Private cvc5 toolchain verification failed; see metadata/cvc5_eunoia_toolchain/output.log",
              file=sys.stderr)
        return 2
    if not args.skip_build:
        build, _ = record_command([str(wrapper), "dune", "build", f"-j{args.jobs}", "theories"],
                                  REPO, args.build_timeout, output / "build")
        if build["exit_code"] != 0 or build["timeout"]:
            print("Build failed; see build/output.log", file=sys.stderr)
            return 2
    compiler = [str(wrapper), "dune", "exec", f"-j{args.jobs}", "--", "rocq", "c",
                "-q", "-color", "no", *rocq_loadpath(REPO),
                "-I", str(REPO / "_build/install/default/lib")]
    # Resolve the real tactic name without calling it or installing a substitute.
    available = {}
    for backend in args.backends:
        directory = output / "preflight" / backend
        directory.mkdir(parents=True)
        probe = directory / "probe.v"
        probe.write_text(prelude(args.extra_import)
                         + f"Ltac eunoia_bench_backend := {BACKENDS[backend]}.\n")
        result, diagnostic = record_command(compiler + [str(probe)], REPO, args.timeout, directory)
        available[backend] = result["exit_code"] == 0 and not result["timeout"]
        if not available[backend]:
            print(f"{backend}: unavailable (preflight/output.log)", flush=True)
    rows = []
    for repeat in range(1, args.repeat + 1):
        # Alternate backend order to reduce a fixed ordering bias; no parallel solvers.
        order = args.backends if repeat % 2 else list(reversed(args.backends))
        for case in cases:
            for backend in order:
                directory = output / "runs" / backend / case["id"] / str(repeat)
                row = {"backend": backend, "case_id": case["id"], "theory": case["theory"],
                       "expected": case["expected"], "repeat": repeat, "solved": False,
                       "status": "unavailable", "exit_code": None, "timeout": False,
                       "process_wall_s": None, "tactic_wall_s": None, "qed_wall_s": None,
                       "tactic_user_s": None, "tactic_system_s": None,
                       "assumptions": None, "new_assumptions": None, "artifact_dir": str(directory)}
                if available[backend]:
                    directory.mkdir(parents=True)
                    proof = directory / "case.v"
                    proof.write_text(source(case, backend, args.extra_import))
                    temporary = directory / "tmp"
                    temporary.mkdir()
                    command = [compiler[0], "env", f"TMPDIR={temporary}", *compiler[1:], str(proof)]
                    result, diagnostic = record_command(command, REPO, args.timeout, directory)
                    row.update({k: result[k] for k in ("exit_code", "timeout", "process_wall_s")})
                    row.update(classify(case, result, diagnostic, proof.with_suffix(".vo").exists()))
                rows.append(row)
                with (output / "attempts.jsonl").open("a") as stream:
                    stream.write(json.dumps(row, sort_keys=True) + "\n")
                print(f"{repeat}/{args.repeat} {backend} {case['id']}: {row['status']}", flush=True)
    summary = summarize(rows)
    write_json(output / "results.json", {"schema_version": 1, "rows": rows, "summary": summary})
    with (output / "results.csv").open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    write_json(output / "summary.json", summary)
    print(json.dumps(summary, indent=2))
    # Unsupported positive goals and timeouts are reported and make the run fail.
    return 0 if all(r["status"] in ("solved", "negative_rejected") for r in rows) else 1


if __name__ == "__main__":
    sys.exit(main())
