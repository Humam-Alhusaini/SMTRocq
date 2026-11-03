#!/usr/bin/env python3
"""Print and compare theorem assumptions using the isolated Rocq toolchain.

Build the modules first. Pass every module and theorem to audit explicitly;
there is deliberately no default list that could miss a new tactic lemma.
For modules not installed yet, --build-loadpaths selects only the explicitly
supplied Dune theory mappings, avoiding overlapping build/install libraries.
"""

import argparse
import json
from pathlib import Path
import re
import subprocess
import tempfile


IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z")
DEPENDENCY = re.compile(r"^([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\s*:", re.M)


def identifier(value):
    if not IDENT.fullmatch(value):
        raise argparse.ArgumentTypeError(f"invalid Rocq identifier: {value!r}")
    return value


def assumptions(output):
    stripped = output.strip()
    if stripped == "Closed under the global context":
        return set()
    if not stripped.startswith("Axioms:"):
        raise ValueError("unrecognized Print Assumptions output")
    body = "\n".join(stripped.splitlines()[1:])
    result = set(DEPENDENCY.findall(body))
    if not result:
        raise ValueError("assumptions were reported but no dependency names were parsed")
    # Fail on an unparsed top-level entry rather than accidentally omitting it.
    for line in stripped.splitlines()[1:]:
        if line and not line[0].isspace() and not DEPENDENCY.match(line):
            raise ValueError(f"unrecognized top-level assumption entry: {line!r}")
    return result


def main():
    root = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--env", type=Path, default=Path(
        "/home/charles/code/friends/.toolchains/smtrocq-env"))
    parser.add_argument("--import", dest="imports", type=identifier, action="append", required=True)
    parser.add_argument("--theorem", type=identifier, action="append", required=True)
    parser.add_argument("--baseline", type=Path,
                        default=root / "docs/eunoia/baseline-assumptions.txt")
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--loadpath", nargs=2, action="append", default=[],
                        metavar=("PATH", "LOGICAL_PREFIX"))
    parser.add_argument("--build-loadpaths", action="store_true",
                        help="use explicit --loadpath mappings without the installed SMTCoq mapping")
    args = parser.parse_args()
    if args.build_loadpaths and not args.loadpath:
        parser.error("--build-loadpaths requires explicit --loadpath mappings")
    baseline = {line.strip() for line in args.baseline.read_text().splitlines()
                if line.strip() and not line.startswith("#")}
    if not baseline or any(not IDENT.fullmatch(name) for name in baseline):
        parser.error("baseline must contain qualified Rocq identifiers, one per line")
    installed = root / "_build/install/default/lib"
    theory = installed / "coq/user-contrib/SMTCoq"
    if not args.build_loadpaths and not theory.is_dir():
        parser.error("build the project before auditing its assumptions")
    output = (args.output_dir or Path(tempfile.mkdtemp(prefix="smtrocq-assumptions."))).resolve()
    output.mkdir(parents=True, exist_ok=True)
    # Audit files and compiler products stay outside the repository.
    if output == root or root in output.parents:
        parser.error("--output-dir must be outside the repository")
    source = output / "AssumptionAudit.v"
    # Resolve user-friendly theorem names inside a local module. Close those
    # imports before printing, so exported Uint63 aliases cannot hide the
    # qualified identities of dependencies in the report.
    commands = [f"Require {module}." for module in args.imports]
    commands.append("Module EunoiaAuditNames.")
    commands.extend(f"Import {module}." for module in args.imports)
    for index, theorem in enumerate(args.theorem):
        commands.append(f"Definition audited_{index} := @{theorem}.")
    commands.extend(["End EunoiaAuditNames.", "Set Printing Width 100."])
    paths = []
    for index, theorem in enumerate(args.theorem):
        stem = output / f"assumptions-{index}"
        if '"' in str(stem) or "\n" in str(stem):
            parser.error("output path cannot contain quotes or newlines")
        commands.append(f'Redirect "{stem}" Print Assumptions EunoiaAuditNames.audited_{index}.')
        paths.append(stem.with_suffix(".out"))
    source.write_text("\n".join(commands) + "\n")
    command = [str(args.env), "rocq", "c", "-I", str(installed)]
    if not args.build_loadpaths:
        command.extend(["-Q", str(theory), "SMTCoq"])
    for path, prefix in args.loadpath:
        if prefix and not IDENT.fullmatch(prefix):
            parser.error(f"invalid logical prefix: {prefix!r}")
        command.extend(["-Q", str(Path(path).resolve()), prefix])
    command.append(str(source))
    run = subprocess.run(command, cwd=root, text=True, capture_output=True)
    (output / "compiler.log").write_text(run.stdout + run.stderr)
    summary = {"command": command, "compiler_exit_code": run.returncode,
               "baseline": str(args.baseline.resolve()), "theorems": []}
    failed = run.returncode != 0
    if run.returncode == 0:
        for theorem, path in zip(args.theorem, paths):
            entry = {"theorem": theorem, "output": str(path)}
            try:
                names = assumptions(path.read_text())
                added = sorted(names - baseline)
                entry.update(assumptions=sorted(names), new_assumptions=added)
                failed = failed or bool(added)
            except (OSError, ValueError) as error:
                entry["error"] = str(error)
                failed = True
            summary["theorems"].append(entry)
    summary["passed"] = not failed
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(f"Assumption audit {'FAILED' if failed else 'passed'}: {output / 'summary.json'}")
    if run.returncode:
        print(run.stdout + run.stderr)
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
