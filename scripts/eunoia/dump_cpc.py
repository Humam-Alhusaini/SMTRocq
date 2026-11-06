#!/usr/bin/env python3
"""Capture reproducible CPC dumps and syntax inventories, never proof acceptance."""

import argparse
from collections import Counter
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import tempfile
import zipfile

from cpc_inventory import input_logic, inventory, signature_rules
from verify_toolchain import add_root_argument, file_sha256, sha256, verify_toolchain


REPOSITORY = Path(__file__).resolve().parents[2]
COMMON_OPTIONS = ["--dump-proofs", "--proof-format=cpc", "--proof-granularity=dsl-rewrite",
                  "--no-proof-allow-trust", "--proof-check=eager", "--check-proofs-complete"]
PROFILES = {
    "default": [],
    "reduced": ["--simplification=none", "--no-static-learning", "--no-ite-simp",
                "--no-unconstrained-simp", "--no-repeat-simp"],
}


def dump(output, toolchain, profiles, inputs, timeout, max_bytes):
    rules = signature_rules(Path(toolchain["signature"]))
    source_revision = subprocess.run(["git", "rev-parse", "HEAD"], cwd=REPOSITORY,
                                     capture_output=True, text=True, check=True).stdout.strip()
    report = {
        "schema": 1,
        "status": "UNVERIFIED_SOLVER_OUTPUT",
        "semantic_verification": "not performed; syntax inventory is not a checker",
        "source_revision": source_revision,
        "toolchain": toolchain,
        "common_options": COMMON_OPTIONS,
        "profiles": {name: PROFILES[name] for name in profiles},
        "timeout_seconds_per_run": timeout,
        "max_dump_bytes": max_bytes,
        "rule_declarations": {},
        "runs": [],
        "totals": {},
    }
    totals = {name: Counter() for name in profiles}
    names = set()
    for source in inputs:
        source = source.resolve(strict=True)
        # Repository-relative names keep input provenance reproducible.
        relative = str(source.relative_to(REPOSITORY))
        name = source.stem
        if name in names:
            raise ValueError(f"duplicate input stem: {name}")
        names.add(name)
        original = source.read_bytes()
        logic = input_logic(original.decode())
        for profile in profiles:
            directory = output / profile
            directory.mkdir(exist_ok=True)
            proof = directory / f"{name}.cpc"
            stderr = directory / f"{name}.stderr"
            command = [toolchain["binary"], *COMMON_OPTIONS, *PROFILES[profile], relative]
            with proof.open("wb") as out, stderr.open("wb") as err:
                result = subprocess.run(command, cwd=REPOSITORY, stdout=out, stderr=err,
                                        timeout=timeout)
            if result.returncode:
                diagnostic = stderr.read_bytes()[:4096].decode(errors="replace")
                raise ValueError(f"cvc5 exited {result.returncode}: {relative} ({profile}): {diagnostic}")
            if source.read_bytes() != original:
                raise ValueError(f"input changed while cvc5 ran: {relative}")
            if proof.stat().st_size > max_bytes:
                raise ValueError(f"dump exceeds --max-dump-bytes: {relative} ({profile})")
            counts = inventory(proof.read_text(), rules)
            totals[profile].update(counts["rules"])
            report["runs"].append({
                "input": relative, "input_sha256": sha256(original), "logic": logic,
                "profile": profile, "argv": command, "cwd": "repository root",
                "exit_code": result.returncode, "solver_result": "unsat",
                "proof": str(proof.relative_to(output)), "proof_sha256": file_sha256(proof),
                "proof_bytes": proof.stat().st_size,
                "stderr": str(stderr.relative_to(output)), "stderr_sha256": file_sha256(stderr),
                **counts,
            })
    for profile, counts in totals.items():
        report["totals"][profile] = dict(sorted(counts.items()))
        report["rule_declarations"].update({rule: rules[rule] for rule in sorted(counts)})
    (output / "inventory.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    return report


def positive_int(value):
    number = int(value)
    if number <= 0:
        raise argparse.ArgumentTypeError("must be positive")
    return number


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    add_root_argument(parser)
    parser.add_argument("--output", required=True, type=Path, help="new directory; never overwrites")
    parser.add_argument("--profile", choices=[*PROFILES, "both"], default="both")
    parser.add_argument("--timeout", type=positive_int, default=30, help="wall seconds per solver run")
    parser.add_argument("--max-dump-bytes", type=positive_int, default=16 * 1024 * 1024,
                        help="reject larger dumps after the solver exits")
    parser.add_argument("inputs", nargs="*", type=Path,
                        help="repository QF_UF/QF_LIA files; default: all uf*/lia* regressions")
    args = parser.parse_args()
    temporary = None
    try:
        output = args.output.absolute()
        if output.exists():
            raise ValueError(f"output already exists: {output}")
        toolchain = verify_toolchain(args.toolchain_root)
        inputs = args.inputs or sorted([
            *REPOSITORY.glob("unit-tests/files/uf*.smt2"),
            *REPOSITORY.glob("unit-tests/files/lia*.smt2"),
        ])
        if not inputs:
            raise ValueError("no regression inputs found")
        profiles = list(PROFILES) if args.profile == "both" else [args.profile]
        temporary = Path(tempfile.mkdtemp(prefix=f".{output.name}-", dir=output.parent))
        report = dump(temporary, toolchain, profiles, inputs, args.timeout, args.max_dump_bytes)
        if output.exists():
            raise ValueError(f"output appeared during capture: {output}")
        temporary.rename(output)
        temporary = None
        print(f"Captured {len(report['runs'])} UNVERIFIED solver dumps in {output}")
        print("Syntax inventory only; no SMTCoq/Rocq proof verification was performed.")
    except (OSError, ValueError, KeyError, tarfile.TarError, zipfile.BadZipFile,
            subprocess.SubprocessError) as error:
        print(f"CPC capture failed: {error}", file=sys.stderr)
        return 1
    finally:
        if temporary is not None:
            shutil.rmtree(temporary)
    return 0


if __name__ == "__main__":
    sys.exit(main())
