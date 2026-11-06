#!/usr/bin/env python3
"""Compare compatible profile artifacts; write numerical results and an HTML chart."""
import argparse
import html
import json
from pathlib import Path
import statistics


def cohort(name):
    if name.startswith("reduced_"):
        return "Reduced UF/LIA"
    return "Original UF" if name.startswith("uf") else "Original LIA"


def aggregate(run, group, phase):
    rounds = []
    for n in range(run["rounds"]):
        rows = [r for r in run["timings"] if r["round"] == n and r["phase"] == phase
                and (group == "All fixtures" or cohort(r["fixture"]) == group)]
        if not rows:
            raise ValueError(f"no rows for round {n}, {group}, {phase}")
        rounds.append(sum((r["user_s"] + r["system_s"]) / r["evaluations"] for r in rows))
    return dict(rounds_cpu_s=rounds, median_cpu_s=statistics.median(rounds),
                min_cpu_s=min(rounds), max_cpu_s=max(rounds))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("before", type=Path)
    ap.add_argument("after", type=Path)
    ap.add_argument("--output", required=True, type=Path, help="new directory for comparison artifacts")
    args = ap.parse_args()
    before, after = [json.loads((p / "summary.json").read_text()) for p in (args.before, args.after)]
    for run in (before, after):
        if not run.get("passed") or any(c["exit_code"] for c in run["commands"]):
            ap.error("both runs must have passed all commands")
    for key in ("repeats", "rounds", "fixtures"):
        if before[key] != after[key]:
            ap.error(f"incompatible {key}")
    for module, info in before["modules"].items():
        if module != "EoRuntime" and info["sha256"] != after["modules"][module]["sha256"]:
            ap.error(f"changed module outside runtime: {module}")
    if (args.before / "version.log").read_bytes() != (args.after / "version.log").read_bytes():
        ap.error("different Rocq/OCaml versions")
    for n in range(before["rounds"]):
        if (args.before / f"Profile{n}.v").read_bytes() != (args.after / f"Profile{n}.v").read_bytes():
            ap.error(f"different generated timing workload in round {n}")
    out = args.output.resolve()
    if out.exists():
        ap.error("--output must be a new directory")
    out.mkdir(parents=True)
    comparisons = []
    for group in ("Original UF", "Original LIA", "Reduced UF/LIA", "All fixtures"):
        for phase in ("repeated_vm", "proof_vm", "qed"):
            b, a = (aggregate(r, group, phase) for r in (before, after))
            comparisons.append(dict(group=group, phase=phase, before=b, after=a,
                                    ratio=a["median_cpu_s"] / b["median_cpu_s"]))
    result = dict(before=str(args.before.resolve()), after=str(args.after.resolve()),
                  note="CPU seconds per complete cohort pass; median of rounds; computation diagnostics only",
                  comparisons=comparisons)
    (out / "comparison.json").write_text(json.dumps(result, indent=2) + "\n")
    lines = ["| Fixtures | Phase | Before CPU s | After CPU s | After / before |",
             "| --- | --- | ---: | ---: | ---: |"]
    for row in comparisons:
        lines.append(f'| {row["group"]} | {row["phase"]} | {row["before"]["median_cpu_s"]:.4f} | '
                     f'{row["after"]["median_cpu_s"]:.4f} | {row["ratio"]:.3f} |')
    (out / "comparison.md").write_text("\n".join(lines) + "\n")
    rows = [r for r in comparisons if r["phase"] == "repeated_vm"]
    maximum = max(r["before"]["median_cpu_s"] for r in rows)
    chart = []
    for row in rows:
        chart.append(f'<h3>{html.escape(row["group"])}</h3>')
        for key, color in (("before", "var(--muted-foreground, #64748b)"),
                           ("after", "var(--chart-2, #0f766e)")):
            value = row[key]["median_cpu_s"]
            chart.append(f'<div class="barrow"><span>{key.title()}</span>'
                         f'<div class="bar" style="width:{value / maximum * 65:.2f}%;background:{color}"></div>'
                         f'<b>{value:.3f} s</b></div>')
    (out / "comparison.html").write_text('''<!doctype html><meta charset="utf-8">
<title>Generated Eunoia replay computation</title><style>
body{font:14px var(--font-sans, system-ui);color:var(--foreground);margin:0}
h2{font-size:20px}h3{margin:20px 0 6px}.chart{height:420px}
.barrow{display:flex;align-items:center;gap:12px;margin:7px 0}
.barrow span{width:56px}.bar{height:23px;border-radius:3px}.barrow b{font-size:14px;white-space:nowrap}
p{color:var(--muted-foreground);line-height:1.5}</style><h2>Generated Eunoia replay computation</h2>
<p>Median CPU seconds per full cohort pass, repeated VM evaluation. Same actual CPC fixtures,
queries, hooks, fuel and generated signature.</p><div class="chart">
''' + "\n".join(chart) + f'</div><p>{before["rounds"]} rounds × {before["repeats"]} evaluations. '
                  'Computation diagnostics; excludes solver, witness search and the external semantic gate. '
                  'This is not an end-to-end tactic benchmark.</p>')
    print("\n".join(lines))
    print(out / "comparison.json")


if __name__ == "__main__":
    main()
