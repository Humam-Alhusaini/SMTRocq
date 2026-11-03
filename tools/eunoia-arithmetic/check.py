#!/usr/bin/env python3
"""Deterministic literal differential tests against the pinned Ethos checker.

No network, installs, or writes outside the repository build directory and the
selected output directory. First build EoArithmeticTests.vo using smtrocq-env
and dune -j2. Run this driver from any directory; use --help for paths.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import random
import resource
import subprocess
import tempfile

PIN = "f97393ea55f03653689e104d0e9c9010ee17780c"
PRIVATE = Path("/home/charles/code/friends/.toolchains")
REPO = Path(__file__).resolve().parents[2]


def corpus():
    cases = []

    def put(op, args, expected):
        cases.append({"op": "eo::" + op, "args": args, "expected": expected})

    def rat(q):
        return f"{q.numerator}/{q.denominator}"

    rng = random.Random(20261103)
    for _ in range(48):
        a, b = [rng.randrange(-10**60, 10**60) for _ in range(2)]
        for op, expected in [("add", a+b), ("mul", a*b), ("zdiv", (a-a % abs(b))//b),
                             ("zmod", a % abs(b))]:
            put(op, [str(a), str(b)], str(expected))
        put("qdiv", [str(a), str(b)], rat(Fraction(a, b)))
        put("gt", [str(a), str(b)], str(a > b).lower())
        put("to_q", [str(a)], f"{a}/1")
        put("is_neg", [str(a)], str(a < 0).lower())
        # Deliberately unreduced spellings, including huge denominators.
        c, d = [rng.randrange(1, 10**40) for _ in range(2)]
        x, y = Fraction(a, c), Fraction(b, d)
        xs, ys = f"{a*6}/{c*6}", f"{b*15}/{d*15}"
        for op, expected in [("add", x+y), ("mul", x*y), ("qdiv", x/y)]:
            put(op, [xs, ys], rat(expected))
        put("gt", [xs, ys], str(x > y).lower())
        put("to_z", [xs], str(x.numerator // x.denominator))
        put("to_q", [xs], rat(x))
        put("neg", [xs], rat(-x))
        put("is_q", [xs], "true")
        put("is_z", [xs], "false")
        put("is_q", [str(a)], "false")

    for a in [-7, -6, -1, 0, 1, 6, 7]:
        for b in [-3, -2, 2, 3]:
            put("zdiv", [str(a), str(b)], str((a-a % abs(b))//b))
            put("zmod", [str(a), str(b)], str(a % abs(b)))
    for op, args, result in [
        ("add", ["1.20", "-0.2"], "1.0"),
        ("mul", ["-0.025", "0.2"], "-0.005"),
        ("to_q", ["-.5"], "-1/2"),
        ("to_z", ["-1.000001"], "-2"),
        ("is_q", ["1.0"], "false"), ("is_z", ["1.0"], "false"),
        ("is_q", ["x"], "false"), ("is_z", ["x"], "false"),
        ("neg", ["-0.0"], "0.0"),
        ("gt", ["1.00", "0.99999999999999999999"], "true"),
        ("qdiv", ["1.25", "-0.50"], "-5/2"),
        ("add", ["1", "-2", "3", "-4"], "-2"),
        ("mul", ["-3/2", "-2/7", "7/3"], "1/1"),
        ("pow", ["-2", "101"], str((-2)**101)),
        ("pow", ["-2/3", "3"], "-8/27"),
        ("pow", ["-0.50", "3"], "-0.125"),
        ("pow", ["2.00", "0"], "1.0"),
        ("pow", ["1", "4294967295"], "1"),
        ("pow", ["1.0", "4294967295"], "1.0"),
        ("pow", ["-1/1", "4294967295"], "-1/1"),
        ("pow", ["0", "0"], "1"),
    ]:
        put(op, args, result)
    for base in [-3, 0, 1, 2, 3, 17]:
        for raw in ["-1/3", "0", "1/2", "1", "1023", "1024", "2049/2", "80.99"]:
            n = Fraction(raw).__floor__()
            count = 0
            if base > 1 and n > 0:
                while n >= base:
                    n //= base
                    count += 1
            put("log", [str(base), raw], str(count))
    for op, args in [
        ("zdiv", ["1", "0"]), ("zmod", ["1", "0"]),
        ("qdiv", ["1", "0"]), ("qdiv", ["1/1", "0/17"]),
        ("qdiv", ["1.0", "-0.0"]), ("add", ["1", "2/1"]),
        ("mul", ["1.0", "1/1"]), ("gt", ["1/1", "1"]),
        ("qdiv", ["1", "1/1"]), ("zdiv", ["1/1", "2/1"]),
        ("zmod", ["1.0", "2.0"]), ("to_q", ["x"]),
        ("to_z", ["x"]), ("neg", ["x"]),
        ("pow", ["2", "-1"]), ("pow", ["2", "4294967296"]),
        ("pow", ["2", "1/1"]), ("log", ["2/1", "4"]),
    ]:
        put(op, args, None)
    return cases


def quote(s):
    return '"' + s.replace('"', '""') + '"'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ethos", type=Path, default=PRIVATE / "ethos-f97393e/ethos")
    parser.add_argument("--ethos-source", type=Path, default=Path("/tmp/smtrocq-ethos"))
    parser.add_argument("--env", type=Path, default=PRIVATE / "smtrocq-env")
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    out = args.out or Path(tempfile.mkdtemp(prefix="eunoia-arithmetic-"))
    out = out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    print(f"Artifacts: {out}", flush=True)
    report = {"ethos_pin": PIN, "commands": []}

    def run(command, log, expected_exit=0):
        command = list(map(str, command))
        result = subprocess.run(command, cwd=REPO, text=True, capture_output=True)
        (out / log).write_text(result.stdout + result.stderr)
        report["commands"].append({"argv": command, "cwd": str(REPO), "exit": result.returncode, "expected_exit": expected_exit})
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
        if result.returncode != expected_exit:
            raise SystemExit(f"Exit {result.returncode}: {command}; see {out / log}")
        return (result.stdout + result.stderr).strip()

    actual = run(["git", "-C", args.ethos_source, "rev-parse", "HEAD"], "ethos-pin.log")
    if actual != PIN:
        raise SystemExit(f"Ethos pin mismatch: {actual}")
    report["ethos_binary_sha256"] = hashlib.sha256(args.ethos.read_bytes()).hexdigest()
    # Build once explicitly before invoking this driver. This avoids a second
    # dune invocation contending with the coordinator's broader build.
    report["rocq_objects_sha256"] = {}
    for name in ["EoSyntax", "EoArithmetic", "EoArithmeticTests"]:
        artifact = REPO / "_build/default/theories/checker/eunoia" / (name + ".vo")
        if not artifact.is_file():
            raise SystemExit("Build first: smtrocq-env dune build -j2 "
                             "theories/checker/eunoia/EoArithmeticTests.vo")
        report["rocq_objects_sha256"][name] = hashlib.sha256(artifact.read_bytes()).hexdigest()
    cases = corpus()
    report["cases"] = len(cases)
    (out / "cases.json").write_text(json.dumps(cases, indent=2) + "\n")
    coq = ['From Stdlib Require Import String List.',
           'From SMTCoq.checker.eunoia Require Import EoSyntax EoArithmetic.',
           'Import ListNotations. Open Scope string_scope. Import EoArithmetic.']
    eo = ['(declare-const Int Type)', '(declare-const Real Type)',
          '(declare-consts <numeral> Int)', '(declare-consts <rational> Real)',
          '(declare-consts <decimal> Real)', '(declare-const x Int)']
    for i, case in enumerate(cases):
        op, xs, expected = case["op"], case["args"], case["expected"]
        coq_args = "; ".join("Symbol " + quote(s) for s in xs)
        coq_value = "None" if expected is None else "Some (Symbol " + quote(expected) + ")"
        coq.append(f'Example c{i} : eval {quote(op)} [{coq_args}] = {coq_value}. '
                   'Proof. vm_compute. reflexivity. Qed.')
        call = f'({op} {" ".join(xs)})'
        if expected is None:
            test = f'(eo::requires (eo::is_ok {call}) false Bool)'
        else:
            test = f'(eo::requires (eo::is_eq {call} {expected}) true Bool)'
        eo.append(f'(define c{i} () true :type {test})')
    eo.append(f'(echo "{len(cases)} literal comparisons passed")')
    (out / "Differential.v").write_text("\n".join(coq) + "\n")
    (out / "differential.eo").write_text("\n".join(eo) + "\n")
    run([args.env, "rocq", "c", "-Q", REPO / "_build/default/theories/checker/eunoia",
         "SMTCoq.checker.eunoia", out / "Differential.v"], "rocq.log")
    run([args.ethos, "--no-normalize-dec", out / "differential.eo"], "ethos.log")
    # Demonstrate that a changed expected value is actually rejected.
    (out / "negative-control.eo").write_text("\n".join(eo[:6]) + "\n" +
        '(define wrong () true :type (eo::requires (eo::is_eq (eo::add 1 2) 4) true Bool))\n')
    diagnostic = run([args.ethos, "--no-normalize-dec", out / "negative-control.eo"],
                     "negative-control.log", expected_exit=-6)
    if "Expected: (eo::requires false true Bool)" not in diagnostic:
        raise SystemExit("Negative control did not report the intended comparison failure")
    print(f"PASS: {len(cases)} cases; Rocq and pinned Ethos exited 0; "
          "changed-result control rejected with SIGABRT (-6).", flush=True)


if __name__ == "__main__":
    main()
