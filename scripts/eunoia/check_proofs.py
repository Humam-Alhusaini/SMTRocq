#!/usr/bin/env python3
"""Audit and independently kernel-check the live checked backend proofs."""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    output = args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix="eunoia-proof-audit-"))
    if output == ROOT or ROOT in output.parents:
        parser.error("proof-audit output must be outside the checkout")
    if args.output:
        output.mkdir(parents=True, exist_ok=False)
    spec = importlib.util.spec_from_file_location("benchmark", ROOT / "benchmarks/eunoia/run.py")
    bench = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(bench)
    wrapper = os.environ.get("EUNOIA_ENV", str(ROOT / "scripts/eunoia/env"))
    mappings = bench.rocq_loadpath(ROOT) + ["-Q", str(ROOT / "_build/default/unit-tests"), "SMTCoq.tests"]
    audit = [sys.executable, "-B", str(ROOT / "tools/audit-eunoia-assumptions.py"),
             "--env", wrapper, "--build-loadpaths", "--output-dir", str(output / "assumptions")]
    for i in range(0, len(mappings), 3):
        audit += ["--loadpath", mappings[i + 1], mappings[i + 2]]
    for module, names in {
        "EunoiaMemo": ["gate_correct", "checker_correct", "checker_b_correct", "checker_eq_correct"],
        "EunoiaScopedAdapter": ["checker_correct", "checker_b_correct", "checker_eq_correct",
                                "scope_assumption_binding", "scope_eval_with_binding",
                                "cached_scope_eval_with_refinement", "prepared_scope_eval_with_refinement"],
        "EunoiaLocal": ["gate_correct"],
        "EunoiaAdapter": ["eval_with_binding", "checker_correct", "encode_atom_refinement",
                          "encode_literal_refinement", "typeof_with_ready_refinement",
                          "prepared_eval_with_refinement", "normalize_source_ordinary",
                          "lookup_encoding_sound", "memo_encoding_refinement",
                          "cached_clause_refinement", "cached_binds_refinement",
                          "cached_bind_terms_refinement", "cached_eval_with_refinement"],
        "EunoiaIntegerEmbedding": ["normalize_ordinary", "positive_denominator",
                                   "fraction_eq_cross", "fraction_le_cross", "fraction_lt_cross",
                                   "fraction_eq_same", "fraction_le_same", "fraction_lt_same",
                                   "floor_integer", "fraction_add", "fraction_mul", "fraction_neg"],
        "EunoiaTactic": ["checker_correct", "checker_b_correct", "checker_eq_correct"],
    }.items():
        prefix = "SMTCoq.checker.eunoia." + module
        audit += ["--import", prefix]
        for name in names:
            audit += ["--theorem", prefix + "." + module + "." + name]
    for module, names in {
        "SMTCoq.checker.eunoia.EoRuntime": ["nil_apply_refinement", "nil_list_apply_refinement",
                                         "resolve_nil_lazy_mode_refinement"],
        "SMTCoq.eunoia_runtime_profile.QueryRefinement": ["native_with_nils_refinement",
                                      "surface_in_with_refinement", "match_pattern_with_refinement"],
        "SMTCoq.eunoia_runtime_profile.SurfaceOutRefinement": ["surface_out_with_refinement"],
    }.items():
        audit += ["--import", module]
        for name in names:
            audit += ["--theorem", module + "." + name]
    public_modules = ("eunoia_tactics", "eunoia_uf", "eunoia_uf_bool", "eunoia_lia", "eunoia_purification", "eunoia_integer_casts")
    for module in public_modules:
        public = "SMTCoq.tests." + module
        audit += ["--import", public]
        for name in re.findall(r"^\s*(?:Lemma|Theorem|Example)\s+(\w+)",
                               (ROOT / "unit-tests" / (module + ".v")).read_text(), re.M):
            audit += ["--theorem", public + "." + name]
    commands = []
    summary = dict(passed=False, commands=commands)
    try:
        kernel = [wrapper, "rocq", "check", "-silent", *mappings,
                  "SMTCoq.eunoia_runtime_profile.QueryRefinement",
                  "SMTCoq.eunoia_runtime_profile.SurfaceOutRefinement",
                  "SMTCoq.checker.eunoia.EunoiaMemoTests",
                  "SMTCoq.checker.eunoia.EunoiaScopedAdapter",
                  "SMTCoq.checker.eunoia.EunoiaIntegerEmbeddingTests",
                  *["SMTCoq.tests." + module for module in public_modules]]
        for name, command in (("assumptions", audit), ("kernel", kernel)):
            result, _ = bench.record_command(command, ROOT, 900, output / name)
            commands.append(result)
            if result["exit_code"] or result["timeout"]:
                raise RuntimeError(f"{name} failed; see {output / name / 'output.log'}")
        summary["passed"] = True
    except Exception as error:
        summary["error"] = str(error)
        raise
    finally:
        (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(f"Proof audit passed: {output}")


if __name__ == "__main__":
    main()
