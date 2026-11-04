#!/usr/bin/env python3
"""Sequential, bounded development probes; never interprets solver output as proof.

Build @install and the witness/backend .cmxs files first. Sources are copied
verbatim, so existing Time/Qed/Print Assumptions boundaries are preserved.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--timeout", type=float, default=30)
    parser.add_argument("--profile", action="store_true")
    parser.add_argument("sources", nargs="+", type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    installed = root / "_build/install/default/lib"
    wrapper = os.environ.get("EUNOIA_ENV", str(next(p for p in Path(__file__).resolve().parents if (p / "dune-project").is_file()) / "scripts/eunoia/env"))
    args.output.mkdir(parents=True, exist_ok=False)
    rows = []
    metadata = {
        "head": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip(),
        "branch": subprocess.check_output(["git", "branch", "--show-current"], cwd=root, text=True).strip(),
        "search_sha256": hashlib.sha256((root / "src/eunoia_witness/search.ml").read_bytes()).hexdigest(),
        "profile": args.profile,
        "timeout_s": args.timeout,
        "cwd": str(root),
        "artifacts": {str(p.relative_to(installed)):
                      hashlib.sha256(p.read_bytes()).hexdigest()
                      for p in sorted(installed.rglob("*.cmxs"))},
    }
    (args.output / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
    for number, source in enumerate(args.sources):
        directory = args.output / (str(number) + "-" + source.parent.parent.name + "-" + source.stem)
        directory.mkdir()
        copied = directory / source.name
        copied.write_bytes(source.read_bytes())
        command = [wrapper, "rocq", "c", "-q", "-color", "no", "-I", str(installed),
                   "-Q", str(installed / "coq/user-contrib/SMTCoq"), "SMTCoq", str(copied.resolve())]
        environment = dict(os.environ)
        environment["EUNOIA_WITNESS_PROFILE"] = "1" if args.profile else "0"
        temporary = directory / "tmp"
        temporary.mkdir()
        environment["TMPDIR"] = str(temporary.resolve())
        row = {"source": str(source.resolve()), "command": command,
               "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
               "loadavg_before": os.getloadavg(), "profile": args.profile}
        started = time.monotonic()
        with (directory / "output.log").open("w") as log:
            process = subprocess.Popen(command, cwd=root, env=environment, stdout=log,
                                       stderr=subprocess.STDOUT, start_new_session=True)
            try:
                process.wait(timeout=args.timeout)
                row["timeout"] = False
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
                row["timeout"] = True
        row.update(exit_code=process.returncode, wall_s=time.monotonic() - started,
                   loadavg_after=os.getloadavg(), log=str(directory / "output.log"))
        rows.append(row)
        (directory / "command.json").write_text(json.dumps(row, indent=2) + "\n")
        (args.output / "results.json").write_text(json.dumps(rows, indent=2) + "\n")
        print(json.dumps(row), flush=True)


if __name__ == "__main__":
    main()
