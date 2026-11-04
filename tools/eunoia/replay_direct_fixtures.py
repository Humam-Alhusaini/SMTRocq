#!/usr/bin/env python3
"""Replay actual CPC fixtures through the proved directly compiled source evaluator.

This checks source-computation compatibility. Semantic acceptance still needs
the exact trace bindings and SMTCoq's separate semantic gate.
"""
import argparse
from pathlib import Path
from replay_fixtures import generate

ROOT = Path(__file__).resolve().parents[2]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    code = '''From Stdlib Require Import String List.
From SMTCoq.checker.eunoia Require Import EoSyntax EoRuntime CpcGenerated TraceReplay LiaTraceReplay.
From SMTCoq.checker.eunoia Require Import CpcDirectRules.
Definition direct_final query roots steps goal :=
 let compute:=fun _ _ name args premises=>CpcDirectRules.derive_context default_primitive 500 query name None args premises in
 match replay_with compute query roots steps with Some env=>lookup goal env|None=>None end.
Definition direct_trace_final query roots commands goal :=
 let compute:=fun _ _ name args premises=>CpcDirectRules.derive_context default_primitive 500 query name None args premises in
 let assuming:=fun _ _ name assumption args premises=>CpcDirectRules.derive_context default_primitive 500 query name (Some assumption) args premises in
 trace_final_with compute assuming query roots commands goal.
'''
    base = ROOT / "tools/eunoia/tests"
    groups = [(sorted((base / "fixtures").glob("uf*.cpc")), False),
              (sorted((base / "fixtures").glob("lia*.cpc")), True),
              (sorted((base / "reduced-fixtures").glob("*.cpc")), True),
              (sorted((base / "integer-fixtures").glob("*.cpc")), True)]
    for paths, scoped in groups:
        if not paths:
            raise ValueError("missing fixture group")
        text = generate(paths, scoped=scoped)
        text = text.replace(" : trace_final ", " : direct_trace_final ")
        text = text.replace(" : final_term ", " : direct_final ")
        code += text
    args.output.write_text(code)


if __name__ == "__main__":
    main()
