#!/usr/bin/env python3
"""Reproduce the pinned native reference build using existing private GMP files."""
import argparse
import json
from pathlib import Path
import subprocess

PIN = "f97393ea55f03653689e104d0e9c9010ee17780c"
PRIVATE = Path("/home/charles/code/friends/.toolchains")

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--source", type=Path, default=Path("/tmp/smtrocq-ethos"))
parser.add_argument("--private", type=Path, default=PRIVATE)
parser.add_argument("--out", type=Path, default=PRIVATE / "ethos-f97393e")
args = parser.parse_args()
pin = subprocess.check_output(["git", "-C", str(args.source), "rev-parse", "HEAD"], text=True).strip()
if pin != PIN:
    raise SystemExit(f"Ethos pin mismatch: {pin}")
if not args.out.resolve().is_relative_to(args.private.resolve()):
    raise SystemExit("Reference binary output must be under the private toolchains directory")
args.out.mkdir(parents=True, exist_ok=True)
command = ["g++", "-std=c++17", "-O1", "-I" + str(args.source / "src"),
           "-I" + str(args.private / "src/gmp-6.3.0"),
           "-I" + str(args.private / "native/include")]
command += sorted(map(str, (args.source / "src").rglob("*.cpp")))
command += [str(args.private / "cvc5-1.4.2/cvc5-Linux-x86_64-static/lib/libgmpxx.a"),
            "-L" + str(args.private / "native/lib"),
            "-Wl,-rpath," + str(args.private / "native/lib"), "-lgmp",
            "-o", str(args.out / "ethos")]
with (args.out / "build.log").open("w") as log:
    result = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT)
(args.out / "build.json").write_text(json.dumps(
    {"pin": pin, "argv": command, "exit": result.returncode}, indent=2) + "\n")
print(f"Exit {result.returncode}; binary/log/command manifest: {args.out}")
raise SystemExit(result.returncode)
