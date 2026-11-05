#!/usr/bin/env python3
"""Focused public-tactic and arithmetic-replay profiles; no benchmark matrix.

Build @install first, then run in an idle isolated checkout. Each compiler is
fresh; Time tactic and Time Qed have matching boundaries in every run. Native
Rocq Profile traces expose VM compilation and kernel typechecking. Optional
temporary instrument.py probes expose the marshaling helper boundary.
"""

import argparse
from collections import defaultdict
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import time


ROOT = Path(__file__).resolve().parents[2]
WRAPPER = os.environ.get("EUNOIA_ENV", str(next(p for p in Path(__file__).resolve().parents if (p / "dune-project").is_file()) / "scripts/eunoia/env"))
CASES = {
    "reflexivity": ("forall (A : Type) (HA : CompDec A) (x : A), x = x", "cvc5_eunoia"),
    "congruence": ("forall (A : Type) (HA : CompDec A) (f : A -> A) (x y : A), "
                   "x = y -> f x = f y", "cvc5_eunoia"),
    "predicate": ("forall (A : Type) (HA : CompDec A) (p : A -> bool) (x y : A), "
                  "x = y -> p x = true -> p y = true", "cvc5_eunoia"),
    "arithmetic_replay": ("forall x : Z, (x + 0 =? x) = true", "backend_lia_replay"),
}
TIMING = re.compile(r"(?:Finished|Completed)(?: (?:failing|successfully))? transaction in "
                    r"([0-9.]+) secs? \(([0-9.]+)u,([0-9.]+)s\)")


def write_json(path, obj):
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n")


def execute(command, directory, timeout):
    start = time.perf_counter()
    with (directory / "output.log").open("w") as log:
        proc = subprocess.Popen(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT,
                                start_new_session=True)
        timed_out = False
        try:
            proc.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(proc.pid, signal.SIGKILL)
            proc.wait()
        except BaseException:
            os.killpg(proc.pid, signal.SIGKILL)
            proc.wait()
            raise
    result = {"command": command, "cwd": str(ROOT), "exit_code": proc.returncode,
              "timeout": timed_out, "process_wall_s": time.perf_counter() - start}
    write_json(directory / "command.json", result)
    return result


def loadpath():
    flags = []
    for dune in sorted((ROOT / "theories").rglob("dune"), key=lambda p: (len(p.parts), str(p))):
        match = re.search(r"\(name\s+(SMTCoq(?:\.[A-Za-z0-9_]+)*)\)", dune.read_text())
        if match:
            flags.extend(["-Q", str(ROOT / "_build/default" / dune.parent.relative_to(ROOT)), match[1]])
    return flags


def trace_summary(path):
    """Self time excludes visible children; suppressed components remain inside it."""
    totals = defaultdict(lambda: {"calls": 0, "inclusive_s": 0., "visible_self_s": 0.})
    stack = []
    for event in json.loads(path.read_text())["traceEvents"]:
        if event["ph"] == "B":
            stack.append([event, 0.])
        elif event["ph"] == "E":
            if not stack or stack[-1][0]["name"] != event["name"]:
                raise ValueError("unbalanced profile events")
            begin, children = stack.pop()
            elapsed = (event["ts"] - begin["ts"]) / 1e6
            row = totals[event["name"]]
            row["calls"] += 1
            row["inclusive_s"] += elapsed
            row["visible_self_s"] += elapsed - children
            if stack:
                stack[-1][1] += elapsed
    if stack:
        raise ValueError("incomplete profile events")
    return dict(totals)


def source(statement, tactic, directory):
    # The replay uses the existing integration-test plugin with production
    # witnesses. It is explicitly a replay, not an arithmetic solver result.
    return ("From SMTCoq Require Import SMTCoq.\n"
            "From SMTCoq.checker.eunoia Require Import EunoiaScopedAdapter.\n"
            "From Stdlib Require Import Bool ZArith.\n"
            'Declare ML Module "rocq-smtcoq.eunoia_backend_test".\n'
            "Local Open Scope Z_scope.\n"
            f"Lemma profile_result : {statement}.\nProof.\n"
            f'Profile "{directory / "tactic"}" Time {tactic}.\n'
            f'Profile "{directory / "qed"}" Time Qed.\n'
            "Print Assumptions profile_result.\n"
            'Goal True. Proof. idtac "EUNOIA_PROFILE_CHECKED". exact I. Qed.\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True, help="new directory outside checkout")
    parser.add_argument("--cases", nargs="+", choices=CASES, default=list(CASES))
    parser.add_argument("--repeat", type=int, default=1)
    parser.add_argument("--timeout", type=float, default=120)
    parser.add_argument("--kernel-check", action="store_true",
                        help="recursive rocq check with VM enabled, no admitted dependencies")
    parser.add_argument("--controls", action="store_true", help="run source, semantic and false-goal controls")
    args = parser.parse_args()
    output = args.output.resolve()
    if output == ROOT or ROOT in output.parents or '"' in str(output) or "\n" in str(output):
        parser.error("output must be an external path without quotes or newlines")
    if args.repeat <= 0 or args.timeout <= 0:
        parser.error("repeat and timeout must be positive")
    output.mkdir(parents=True, exist_ok=False)
    # A consumer plugin can stay up to date when a dependency's implementation
    # changes but its interface does not. Build the measured library itself.
    build_dir = output / "build"
    build_dir.mkdir()
    build = execute([WRAPPER, "dune", "build", "-j2", "src/eunoia_backend/eunoia_backend.cmxs",
                     "src/eunoia_backend/tests/integration/backend_test_plugin.cmxs"], build_dir, args.timeout)
    if build["exit_code"] != 0 or build["timeout"]:
        return 1
    metadata = {"argv": os.sys.argv, "root": str(ROOT), "cases": CASES,
                "loadavg_start": os.getloadavg(), "source_sha256": {}, "artifact_sha256": {},
                "profile_components": os.environ.get("ROCQ_PROFILE_COMPONENTS", "default"),
                "single_kernel_acceptance": os.environ.get("EUNOIA_SINGLE_KERNEL_ACCEPTANCE", "1"),
                "trace_constants": os.environ.get("EUNOIA_TRACE_CONSTANTS", "1")}
    for command in (["git", "rev-parse", "HEAD"], ["git", "branch", "--show-current"],
                    ["git", "status", "--short"], [WRAPPER, "rocq", "c", "--version"]):
        result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, check=True)
        metadata[" ".join(command)] = result.stdout
    for relative in ("src/eunoia_backend/eunoiaRocq.ml", "src/eunoia_backend/eunoiaBackend.ml",
                     "tools/eunoia-profile/run.py", "tools/eunoia-profile/Controls.v",
                     "theories/checker/eunoia/EunoiaTactic.v"):
        metadata["source_sha256"][relative] = hashlib.sha256((ROOT / relative).read_bytes()).hexdigest()
    for relative in ("src/eunoia_backend/eunoia_backend.cmxs",
                     "src/eunoia_backend/tests/integration/backend_test_plugin.cmxs"):
        metadata["artifact_sha256"][relative] = hashlib.sha256(
            (ROOT / "_build/default" / relative).read_bytes()).hexdigest()
    write_json(output / "metadata.json", metadata)
    flags = loadpath()
    rows = []
    failed = False
    for repetition in range(1, args.repeat + 1):
        for case in args.cases:
            directory = output / f"{case}-{repetition}"
            directory.mkdir()
            statement, tactic = CASES[case]
            (directory / "Case.v").write_text(source(statement, tactic, directory))
            local_flags = [*flags, "-Q", str(directory), "EunoiaProfile"]
            command = [WRAPPER, "dune", "exec", "-j2", "--", "rocq", "c", "-q",
                       "-color", "no", *local_flags, "-I", str(ROOT / "_build/install/default/lib"),
                       str(directory / "Case.v")]
            row = {"case": case, "repeat": repetition, **execute(command, directory, args.timeout)}
            log = (directory / "output.log").read_text()
            timings = TIMING.findall(log)
            checked = (row["exit_code"] == 0 and not row["timeout"] and len(timings) == 2
                       and (directory / "Case.vo").is_file() and "EUNOIA_PROFILE_CHECKED" in log)
            row["checked"] = checked
            if checked:
                row["tactic_wall_s"], row["qed_wall_s"] = [float(t[0]) for t in timings]
                for stage in ("tactic", "qed"):
                    summary = trace_summary(directory / f"{stage}.json")
                    row[f"{stage}_profile"] = summary
                    write_json(directory / f"{stage}-summary.json", summary)
                audit_dir = directory / "audit"
                audit_dir.mkdir()
                audit = execute(["python3", "-B", str(ROOT / "tools/audit-eunoia-assumptions.py"),
                                 "--import", "EunoiaProfile.Case", "--theorem", "profile_result",
                                 "--loadpath", str(directory), "EunoiaProfile",
                                 "--output-dir", str(audit_dir)], audit_dir, args.timeout)
                row["audit_exit_code"] = audit["exit_code"]
                failed |= audit["exit_code"] != 0 or audit["timeout"]
                if args.kernel_check:
                    check_dir = directory / "kernel"
                    check_dir.mkdir()
                    check = execute([WRAPPER, "rocq", "check", "-silent", "-bytecode-compiler", "yes",
                                     *local_flags, "EunoiaProfile.Case"], check_dir, args.timeout)
                    row["kernel_exit_code"] = check["exit_code"]
                    failed |= check["exit_code"] != 0 or check["timeout"]
            failed |= not checked
            rows.append(row)
            write_json(output / "results.json", rows)
            print(f"{case} {repetition}: checked={checked}, exit={row['exit_code']}, "
                  f"tactic={row.get('tactic_wall_s')}, Qed={row.get('qed_wall_s')}", flush=True)
    if args.controls:
        directory = output / "controls"
        directory.mkdir()
        (directory / "Controls.v").write_bytes(Path(__file__).with_name("Controls.v").read_bytes())
        local_flags = [*flags, "-Q", str(directory), "EunoiaProfile"]
        execution = execute([WRAPPER, "dune", "exec", "-j2", "--", "rocq", "c", "-q",
                             *local_flags, "-I", str(ROOT / "_build/install/default/lib"),
                             str(directory / "Controls.v")], directory, args.timeout)
        failed |= execution["exit_code"] != 0 or execution["timeout"]
        if execution["exit_code"] == 0 and not execution["timeout"]:
            audit_dir = directory / "audit"
            audit_dir.mkdir()
            audit = execute(["python3", "-B", str(ROOT / "tools/audit-eunoia-assumptions.py"),
                             "--import", "EunoiaProfile.Controls", "--theorem", "false_controls",
                             "--theorem", "source_controls", "--theorem", "local_controls",
                             "--loadpath", str(directory), "EunoiaProfile",
                             "--output-dir", str(audit_dir)], audit_dir, args.timeout)
            failed |= audit["exit_code"] != 0 or audit["timeout"]
            if args.kernel_check:
                check_dir = directory / "kernel"
                check_dir.mkdir()
                check = execute([WRAPPER, "rocq", "check", "-silent", "-bytecode-compiler", "yes",
                                 *local_flags, "EunoiaProfile.Controls"], check_dir, args.timeout)
                failed |= check["exit_code"] != 0 or check["timeout"]
        print(f"controls: exit={execution['exit_code']}", flush=True)
    metadata["loadavg_end"] = os.getloadavg()
    write_json(output / "metadata.json", metadata)
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
