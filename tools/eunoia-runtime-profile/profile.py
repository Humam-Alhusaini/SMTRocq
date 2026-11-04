#!/usr/bin/env python3
"""Isolated Rocq VM timings for actual generated CPC fixture computation.

No solver or semantic gate is replaced: these are computation diagnostics,
using the existing fixture decoder, queries, hooks, fuel and replay functions.
Artifacts, commands, hashes, exit codes and raw logs are retained outside Git.
"""
import argparse
import hashlib
import json
import os
import platform
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools/eunoia"))
from replay_fixtures import decode, generate
from compile import atom, parse, seq

ENV = Path(os.environ.get("EUNOIA_ENV", str(next(p for p in Path(__file__).resolve().parents if (p / "dune-project").is_file()) / "scripts/eunoia/env")))
MODULES = ("EoSyntax", "EoRuntime", "EoArithmetic", "EoOrder", "CpcGenerated",
           "TraceReplay", "LiaTraceReplay")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fixtures():
    base = ROOT / "tools/eunoia/tests"
    return [(p, False) for p in sorted((base / "fixtures").glob("uf*.cpc"))] + [
        (p, True) for p in sorted((base / "fixtures").glob("lia*.cpc"))] + [
        (p, True) for p in sorted((base / "reduced-fixtures").glob("*.cpc"))]


def source(paths, repeats):
    parts = []
    for path, scoped in paths:
        code = generate([path], scoped=scoped)
        # Time repeated evaluation while the goal remains unchanged. Each VM
        # invocation computes the complete replay and compares the actual result.
        # Then separately time proof-producing reduction and kernel Qed checking.
        example = re.search(r"Example (\w+) : (.*) = Some \(Symbol \"false\"\)\.", code)
        if example is None:
            raise ValueError(f"unrecognized generated example for {path}")
        name, computation = example.groups()
        phases = [
            f'Proof. idtac "PROFILE {name} repeated_vm".',
            f'Time do {repeats} (let result := eval vm_compute in ({computation}) in',
            '  constr_eq result constr:(Some (Symbol "false"))).',
            f'idtac "PROFILE {name} proof_vm". Time vm_compute.',
            f'idtac "PROFILE {name} reflexivity". Time reflexivity.',
            'Time Qed.',
        ]
        parts.append(code.replace("Proof. vm_compute. reflexivity. Qed.", "\n".join(phases)))
    return "\n".join(parts)


def timings(log, repeats):
    rows, label = [], None
    for line in log.splitlines():
        if line.startswith("PROFILE "):
            _, name, phase = line.split()
            label = (name, phase)
        match = re.match(r"Finished transaction in ([\d.]+) secs \(([\d.]+)u,([\d.]+)s\)", line)
        if match and label:
            wall, user, system = map(float, match.groups())
            rows.append(dict(fixture=label[0].removesuffix("_all_steps"), phase=label[1],
                             wall_s=wall, user_s=user, system_s=system,
                             evaluations=repeats if label[1] == "repeated_vm" else 1))
            label = (label[0], "qed") if label[1] == "reflexivity" else None
    return rows


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output", required=True, type=Path, help="new artifact directory outside the checkout")
    ap.add_argument("--runtime", type=Path, default=ROOT / "theories/checker/eunoia/EoRuntime.v")
    ap.add_argument("--repeats", type=int, default=20)
    ap.add_argument("--rounds", type=int, default=3)
    ap.add_argument("--fixture", action="append", help="optional fixture stem, repeatable; default all 29")
    ap.add_argument("--refinement", type=Path, help="optional pointwise refinement proof to compile, audit and kernel-check")
    ap.add_argument("--timeout", type=int, default=600, help="per-process limit in seconds")
    args = ap.parse_args()
    out = args.output.resolve()
    if out == ROOT or ROOT in out.parents or out.exists():
        ap.error("--output must be a new directory outside the checkout")
    if min(args.repeats, args.rounds, args.timeout) < 1:
        ap.error("repeats, rounds and timeout must be positive")
    paths = fixtures()
    if args.fixture:
        unknown = set(args.fixture) - {p.stem for p, _ in paths}
        if unknown:
            ap.error(f"unknown fixtures: {sorted(unknown)}")
        paths = [(p, s) for p, s in paths if p.stem in args.fixture]
    out.mkdir(parents=True)
    summary = dict(command=sys.argv, root=str(ROOT), runtime=str(args.runtime.resolve()),
                   repeats=args.repeats, rounds=args.rounds, timeout_s=args.timeout,
                   git_head=subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
                   git_status=subprocess.check_output(["git", "status", "--short"], cwd=ROOT, text=True),
                   platform=platform.platform(), cpu_count=os.cpu_count(),
                   profiler_sha256=digest(Path(__file__)),
                   modules={}, fixtures=[], commands=[], timings=[])

    def save():
        (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")

    def run(command, stem):
        start = time.monotonic()
        with (out / f"{stem}.log").open("w") as log:
            try:
                result = subprocess.run(list(map(str, command)), cwd=out, stdout=log,
                                        stderr=subprocess.STDOUT, timeout=args.timeout,
                                        env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"})
                code = result.returncode
            except subprocess.TimeoutExpired:
                code = 124
        summary["commands"].append(dict(command=list(map(str, command)), cwd=str(out),
                                        exit_code=code, wall_s=time.monotonic() - start,
                                        log=str(out / f"{stem}.log")))
        save()
        if code:
            raise RuntimeError(f"exit {code}: {stem}; see {out / (stem + '.log')}")
        return (out / f"{stem}.log").read_text()

    try:
        run([ENV, "rocq", "--version"], "version")
        for module in MODULES:
            if module == "EoRuntime":
                path = args.runtime
            elif module in ("TraceReplay", "LiaTraceReplay"):
                path = ROOT / f"tools/eunoia/tests/{module}.v"
            else:
                path = ROOT / f"theories/checker/eunoia/{module}.v"
            shutil.copyfile(path, out / f"{module}.v")
            summary["modules"][module] = dict(source=str(path.resolve()), sha256=digest(path))
            run([ENV, "rocq", "compile", "-q", "-Q", ".", "SMTCoq.checker.eunoia", f"{module}.v"], module)
        for path, scoped in paths:
            _, _, commands, _ = decode(path, scoped=scoped)
            kinds = [atom(seq(c)[0]) for c in seq(parse(path.read_text(), path)[1])]
            summary["fixtures"].append(dict(path=str(path.relative_to(ROOT)), sha256=digest(path),
                                            scoped=scoped, commands=len(commands),
                                            steps=kinds.count("step") + kinds.count("step-pop"),
                                            pushes=kinds.count("assume-push")))
        if args.refinement:
            shutil.copyfile(args.refinement, out / "SurfaceOutRefinement.v")
            summary["refinement_sha256"] = digest(args.refinement)
            log = run([ENV, "rocq", "compile", "-q", "-Q", ".", "SMTCoq.checker.eunoia",
                       "SurfaceOutRefinement.v"], "SurfaceOutRefinement")
            if log.count("Closed under the global context") != 2:
                raise RuntimeError("refinement lemmas are not closed under the global context")
            run([ENV, "rocq", "check", "-silent", "-Q", ".", "SMTCoq.checker.eunoia",
                 "SMTCoq.checker.eunoia.SurfaceOutRefinement"], "SurfaceOutRefinement-kernel")
        workload = source(paths, args.repeats)
        for round_number in range(args.rounds):
            # Reverse fixture order on alternating rounds to expose order effects.
            if round_number % 2:
                workload = source(list(reversed(paths)), args.repeats)
            else:
                workload = source(paths, args.repeats)
            module = f"Profile{round_number}"
            (out / f"{module}.v").write_text(workload)
            log = run([ENV, "rocq", "compile", "-q", "-Q", ".", "SMTCoq.checker.eunoia", f"{module}.v"], module)
            rows = timings(log, args.repeats)
            if len(rows) != len(paths) * 4 or log.count("Closed under the global context") != len(paths):
                raise RuntimeError(f"incomplete timing/assumption output in {module}.log")
            summary["timings"].extend(dict(round=round_number, **row) for row in rows)
            save()
            if round_number == 0:
                # Subsequent rounds contain the same examples (possibly in
                # reverse order). Check the complete workload independently once.
                run([ENV, "rocq", "check", "-silent", "-Q", ".", "SMTCoq.checker.eunoia",
                     f"SMTCoq.checker.eunoia.{module}"], f"{module}-kernel")
        summary["passed"] = True
        save()
        print(out / "summary.json")
    except Exception as error:
        summary.update(passed=False, error=str(error))
        save()
        raise


if __name__ == "__main__":
    main()
