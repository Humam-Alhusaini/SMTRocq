#!/usr/bin/env python3
"""Inventory actual cvc5 CPC output; this is not a Rocq proof replay."""

import argparse
import collections
import hashlib
import json
import pathlib
import re
import subprocess


INT_PRELUDE = """(set-logic QF_UFLIA)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(declare-fun f (Int) Int)
(declare-fun g (Int Int) Int)
(declare-fun P (Int) Bool)
"""
BOOL_PRELUDE = """(set-logic QF_UF)
(declare-fun x () Bool)
(declare-fun y () Bool)
"""
CASES = {
    "int-congr-reverse": (INT_PRELUDE,
        "(assert (= y x))\n(assert (not (= (f x) (f y))))"),
    "int-symm": (INT_PRELUDE,
        "(assert (= (f x) (f y)))\n(assert (not (= (f y) (f x))))"),
    "int-trans": (INT_PRELUDE,
        "(assert (= x y))\n(assert (= y z))\n(assert (not (= x z)))"),
    "int-congr2": (INT_PRELUDE,
        "(assert (= x y))\n(assert (not (= (g z x) (g z y))))"),
    "int-neg-symm": (INT_PRELUDE,
        "(assert (not (= x y)))\n(assert (= y x))"),
    "int-predicate": (INT_PRELUDE,
        "(assert (= x y))\n(assert (P x))\n(assert (not (P y)))"),
    "int-affine-uf": (INT_PRELUDE,
        "(assert (= (+ x 1) (+ y 1)))\n(assert (not (= (f y) (f x))))"),
    "bool-domain-congr": (BOOL_PRELUDE.replace("QF_UF", "QF_UFLIA")
        + "(declare-fun f (Bool) Int)\n",
        "(assert (= x y))\n(assert (not (= (f x) (f y))))"),
    "bool-result-congr": (BOOL_PRELUDE + "(declare-fun f (Bool) Bool)\n",
        "(assert (= x y))\n(assert (f x))\n(assert (not (f y)))"),
    "bool-neg-symm": (BOOL_PRELUDE,
        "(assert (not (= x y)))\n(assert (= y x))"),
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cvc5", required=True, type=pathlib.Path)
    parser.add_argument("--out", required=True, type=pathlib.Path)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    repo = pathlib.Path(__file__).resolve().parents[2]
    inputs = sorted((repo / "unit-tests/files").glob("uf*.smt2"))
    for name, (prelude, assertions) in sorted(CASES.items()):
        source = args.out / (name + ".smt2")
        source.write_text(prelude + assertions + "\n(check-sat)\n(exit)\n")
        inputs.append(source)
    results = []
    for source in inputs:
        command = [str(args.cvc5), "--dump-proofs", "--proof-format=cpc",
                   "--check-proofs", "--check-proofs-complete", str(source)]
        run = subprocess.run(command, capture_output=True, text=True, timeout=30)
        (args.out / (source.stem + ".cpc")).write_text(run.stdout)
        (args.out / (source.stem + ".stderr")).write_text(run.stderr)
        if run.returncode or run.stdout.splitlines()[:1] != ["unsat"]:
            raise RuntimeError(f"{source}: exit {run.returncode}: {run.stderr}")
        rules = collections.Counter(re.findall(r":rule ([^\s)]+)", run.stdout))
        result = dict(source=str(source), command=command, exit_code=run.returncode,
                      answer="unsat", steps=sum(rules.values()),
                      rules=dict(sorted(rules.items())),
                      source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                      proof_sha256=hashlib.sha256(run.stdout.encode()).hexdigest())
        results.append(result)
        print(f"{source.name}: exit 0, unsat, {result['steps']} steps, {result['rules']}")
    (args.out / "inventory.json").write_text(json.dumps(results, indent=2) + "\n")


if __name__ == "__main__":
    main()
