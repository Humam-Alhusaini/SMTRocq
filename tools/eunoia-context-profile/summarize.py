#!/usr/bin/env python3
"""Extract raw, non-overlapping transaction timings from retained checked runs."""
import argparse
import json
from pathlib import Path
import re

TIMING = re.compile(r"(?:Finished|Completed)(?: (?:failing|successfully))? transaction in "
                   r"([0-9.]+) secs? \(([0-9.]+)u,([0-9.]+)s\)")
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("runs", type=Path, nargs="+")
args = parser.parse_args()
rows = []
for run in args.runs:
    metadata = json.loads((run / "metadata.json").read_text())
    for result in json.loads((run / "results.json").read_text()):
        if not result["checked"] or result["audit_exit_code"] != 0:
            raise ValueError("unchecked or unaudited result")
        timings = TIMING.findall((run / f'{result["case"]}-{result["repeat"]}' / "output.log").read_text())
        if len(timings) != 2:
            raise ValueError("expected exactly one tactic and one Qed transaction")
        row = {"run": str(run), "case": result["case"], "repeat": result["repeat"],
               "process_wall_s": result["process_wall_s"],
               "vm_conv_s": result["tactic_profile"]["vm_conv"]["inclusive_s"],
               "loadavg_start": metadata["loadavg_start"], "loadavg_end": metadata["loadavg_end"]}
        for stage, values in zip(("tactic", "qed"), timings):
            row[stage] = dict(zip(("wall_s", "user_s", "system_s"), map(float, values)))
        rows.append(row)
print(json.dumps(rows, indent=2))
