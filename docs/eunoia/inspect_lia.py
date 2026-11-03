#!/usr/bin/env python3
"""Collect cvc5 CPC text and rule counts. This is NOT a proof checker."""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess


# Negations of integer goals in unit-tests/lfsc_tactics.v, Section LIA,
# and examples/Example.v. These are explicit SMT-LIB transcriptions, not
# output of the Rocq tactic/reifier. Prop and Boolean variants share a case.
TACTIC_GOALS = {
    "refl": (
        "QF_LIA", "(declare-const a Int)\n(declare-const b Int)",
        "(and (= a a) (= b b))"),
    "eq-symm": (
        "QF_LIA", "(declare-const a Int)\n(declare-const b Int)",
        "(= (= a b) (= b a))"),
    "lt-plus1": (
        "QF_LIA", "(declare-const a Int)\n(declare-const b Int)",
        "(=> (< a b) (< a (+ b 1)))"),
    "ge-trichotomy": (
        "QF_LIA", "(declare-const x Int)\n(declare-const y Int)",
        "(=> (>= x y) (or (< y x) (= x y)))"),
    "uf-lia": (
        "QF_UFLIA", "(declare-fun f (Int) Int)\n(declare-const a Int)",
        "(=> (> (f a) 1) (or (>= (+ (f a) 1) 2) (= (f a) 30)))"),
    "vacuous-eq": (
        "QF_LIA", "(declare-const x Int)",
        "(=> (= x 0) (>= 8 0))"),
    "vacuous-lt": (
        "QF_LIA", "(declare-const x Int)",
        "(=> (not (< x 0)) (>= 8 0))"),
    "shift": (
        "QF_LIA", "(declare-const a Int)\n(declare-const b Int)",
        "(=> (< a b) (< (+ a 2) (+ b 3)))"),
    "lt-plus10": (
        "QF_LIA", "(declare-const a Int)\n(declare-const b Int)",
        "(=> (< a b) (< a (+ b 10)))"),
    "parity-ite": (
        "QF_LIA",
        "(declare-const b1 Bool)\n(declare-const b2 Bool)\n"
        "(declare-const x1 Int)\n(declare-const x2 Int)",
        "(=> (ite b1 "
        "(ite b2 (= (+ (* 2 x1) 1) (+ (* 2 x2) 1)) "
        "(= (+ (* 2 x1) 1) (* 2 x2))) "
        "(ite b2 (= (* 2 x1) (+ (* 2 x2) 1)) (= (* 2 x1) (* 2 x2)))) "
        "(and (=> b1 b2) (=> b2 b1) (= x1 x2)))"),
    "uf-rewrite": (
        "QF_UFLIA",
        "(declare-const x Int)\n(declare-const y Int)\n"
        "(declare-fun f (Int) Int)",
        "(=> (= x (+ y 1)) (= (f y) (f (- x 1))))"),
}


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cvc5", required=True, type=Path)
    parser.add_argument("--signature", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    args.output.mkdir(parents=True, exist_ok=True)
    version = subprocess.run([str(args.cvc5), "--version"], check=True,
                             capture_output=True, text=True)
    report = {
        "purpose": "CPC text inventory only; no CPC proof was checked",
        "cvc5": str(args.cvc5),
        "cvc5_sha256": sha256(args.cvc5),
        "version": version.stdout,
        "signature": str(args.signature),
        "signature_sha256": sha256(args.signature),
        "samples": [],
    }
    inputs = sorted((root / "unit-tests/files").glob("lia*.smt2"))
    for name, (logic, declarations, goal) in TACTIC_GOALS.items():
        path = args.output / f"tactic-{name}.smt2"
        path.write_text(f"(set-logic {logic})\n{declarations}\n"
                        f"(assert (not {goal}))\n(check-sat)\n(exit)\n")
        inputs.append(path)
    for path in inputs:
        command = [str(args.cvc5), "--dump-proofs", "--proof-format=cpc",
                   str(path)]
        result = subprocess.run(command, capture_output=True, timeout=60)
        stdout = result.stdout.decode()
        proof_path = args.output / f"{path.stem}.cpc"
        proof_path.write_bytes(result.stdout)
        (args.output / f"{path.stem}.stderr").write_bytes(result.stderr)
        rules = Counter(re.findall(r":rule\s+([^\s()]+)", stdout))
        sample = {
            "input": str(path), "input_sha256": sha256(path),
            "command": command, "exit_code": result.returncode,
            "solver_status": stdout.splitlines()[0] if stdout else "",
            "cpc_sha256": sha256(proof_path),
            "steps_including_step_pop": sum(rules.values()),
            "root_assumptions": len(re.findall(r"\(assume\s", stdout)),
            "scope_assumptions": len(re.findall(r"\(assume-push\s", stdout)),
            "rules": dict(sorted(rules.items())),
        }
        report["samples"].append(sample)
        print(f"{path.stem}: exit {result.returncode}, "
              f"solver {sample['solver_status']}, {sum(rules.values())} steps")
        if result.returncode != 0 or sample["solver_status"] != "unsat" or not rules:
            raise RuntimeError(f"Could not collect expected CPC text: {path}")
    (args.output / "inventory.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
