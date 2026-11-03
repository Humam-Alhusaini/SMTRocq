#!/usr/bin/env python3
"""Summarize completed and interrupted Search.produce stages from stderr."""
import argparse
import json
from pathlib import Path
import re


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("log", type=Path)
    args = parser.parse_args()
    pattern = re.compile(r"EUNOIA_WITNESS id=(\d+) stage=(\S+) event=(\S+) "
                         r"cpu_s=([\d.]+) slots=(\d+) pairs=(\d+) formulas=(\d+)")
    open_stages, stages = {}, []
    for line in args.log.read_text().splitlines():
        match = pattern.fullmatch(line)
        if not match:
            continue
        sequence, stage, event, cpu, slots, pairs, formulas = match.groups()
        key = (int(sequence), stage)
        sample = dict(id=int(sequence), stage=stage, event=event, cpu_s=float(cpu),
                      slots=int(slots), pairs=int(pairs), formulas=int(formulas))
        if event == "begin":
            open_stages[key] = sample
        else:
            start = open_stages.pop(key)
            stages.append(dict(sample, stage_cpu_s=sample["cpu_s"] - start["cpu_s"],
                               new_slots=sample["slots"] - start["slots"],
                               new_pairs=sample["pairs"] - start["pairs"]))
    print(json.dumps(dict(slowest_completed=sorted(stages, key=lambda s: s["stage_cpu_s"],
                                                  reverse=True)[:12],
                          interrupted=list(open_stages.values())), indent=2))


if __name__ == "__main__":
    main()
