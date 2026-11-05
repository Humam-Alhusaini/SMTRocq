#!/usr/bin/env python3
"""Replay captured CPC proofs using signature-generated checked rule records."""
import argparse
import json
from pathlib import Path
import re
from replay_fixtures import generate

ROOT = Path(__file__).resolve().parents[2]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    base = ROOT / "tools/eunoia/tests"
    groups = [(sorted((base / "fixtures").glob("uf*.cpc")), False),
              (sorted((base / "fixtures").glob("lia*.cpc")), True),
              (sorted((base / "reduced-fixtures").glob("*.cpc")), True),
              (sorted((base / "integer-fixtures").glob("*.cpc")), True)]
    if any(not paths for paths, _ in groups):
        raise ValueError("missing fixture group")
    inventory = json.loads((ROOT / "tools/eunoia/cpc-specialized-manifest.json").read_text())["implementations"]
    used = {name for paths, _ in groups for path in paths
            for name in re.findall(r":rule\s+([^\s)]+)", path.read_text())}
    if used - inventory.keys():
        raise ValueError("fixture uses rules absent from the specialized inventory")
    records = ";".join("CpcSpecialized." + inventory[name] for name in sorted(used))
    code = '''From Stdlib Require Import String List.
From SMTCoq.checker.eunoia Require Import EoSyntax EoRuntime CpcGenerated TraceReplay LiaTraceReplay.
From SMTCoq.checker.eunoia Require Import EoSpecialized CpcSpecialized.
Import ListNotations.
'''
    code += "Definition implementations := [" + records + "].\n"
    code += '''Definition specialized_final query roots steps goal :=
 let compute:=fun _ _ name args premises=>EoSpecialized.derive_context implementations default_primitive 500 query name None args premises in
 match replay_with compute query roots steps with Some env=>lookup goal env|None=>None end.
Definition specialized_trace_final query roots commands goal :=
 let compute:=fun _ _ name args premises=>EoSpecialized.derive_context implementations default_primitive 500 query name None args premises in
 let assuming:=fun _ _ name assumption args premises=>EoSpecialized.derive_context implementations default_primitive 500 query name (Some assumption) args premises in
 trace_final_with compute assuming query roots commands goal.
'''
    for paths, scoped in groups:
        text = generate(paths, scoped=scoped)
        text = text.replace(" : trace_final ", " : specialized_trace_final ")
        text = text.replace(" : final_term ", " : specialized_final ")
        code += text
    args.output.write_text(code)


if __name__ == "__main__":
    main()
