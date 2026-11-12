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
    mappings = bench.rocq_loadpath(ROOT) + [
        "-Q", str(ROOT / "_build/default/unit-tests"), "SMTCoq.tests",
        "-Q", str(ROOT / "_build/default/tools/eunoia-runtime-profile"),
        "SMTCoq.eunoia_runtime_profile",
        "-Q", str(ROOT / "_build/default/tools/eunoia-kernel-acceptance-probe"),
        "SMTCoq.eunoia_kernel_acceptance_probe",
        "-Q", str(ROOT / "_build/default/src/eunoia_backend/tests/integration"),
        "SMTCoq.eunoia_backend_tests"]
    audit = [sys.executable, "-B", str(ROOT / "tools/audit-eunoia-assumptions.py"),
             "--env", wrapper, "--build-loadpaths", "--output-dir", str(output / "assumptions")]
    for i in range(0, len(mappings), 3):
        audit += ["--loadpath", mappings[i + 1], mappings[i + 2]]
    prefix = "SMTCoq.checker.eunoia.CpcSpecialized"
    audit += ["--import", prefix, "--theorem", prefix + ".CpcSpecialized.rules_correct"]
    for module, names in {
        "EoModelDagCache": ["run_correct", "compile_correct", "cached_correct"],
        "EunoiaModelDag": ["body_reference", "prepare_valid", "encode_literal_cached_correct", "encoding_entries_refinement"],
        "EunoiaModelDagCheck": ["checker_refinement", "checker_correct", "checker_b_refinement", "checker_b_correct", "checker_eq_refinement", "checker_eq_correct"],
        "EunoiaProgramIndexFlat": ["flat_step_ext", "flat_run_ext", "flat_checker_ext", "checker_refinement", "checker_correct", "checker_b_refinement", "checker_b_correct", "checker_eq_refinement", "checker_eq_correct"],
        "EunoiaProgramIndexScoped": ["checker_refinement", "checker_correct", "checker_b_refinement", "checker_b_correct", "checker_eq_refinement", "checker_eq_correct"],
        "EoRename": ["refinement"],
        "EoDirect": ["compile_refinement", "run_program_correct", "call_compiled_correct"],
        "CpcDirect": ["dispatch_correct"],
        "CpcDirectEntry": ["choose_correct", "dispatch_correct"],
        "CpcDirectEval": ["evaluate_correct"],
        "CpcDirectRules": ["run_rule_correct", "run_surface_correct", "derive_context_correct"],
        "EoSpecialized": ["prepare_one_correct", "prepare_one_ext", "find_key", "run_using_correct", "run_surface_correct", "derive_context_correct"],
        "EunoiaSpecialized": ["checker_refinement", "checker_correct", "checker_b_refinement", "checker_b_correct", "checker_eq_refinement", "checker_eq_correct"],
        "EunoiaSpecializedScoped": ["checker_refinement", "checker_correct", "checker_b_refinement", "checker_b_correct", "checker_eq_refinement", "checker_eq_correct"],
        "EunoiaSpecializedFlat": ["flat_step_ext", "flat_run_ext", "flat_checker_ext", "checker_refinement", "checker_correct", "checker_b_refinement", "checker_b_correct", "checker_eq_refinement", "checker_eq_correct"],
        "EunoiaDirect": ["checker_refinement", "checker_correct", "checker_b_refinement", "checker_b_correct", "checker_eq_refinement", "checker_eq_correct"],
        "EunoiaDirectScoped": ["checker_refinement", "checker_correct", "checker_b_refinement", "checker_b_correct", "checker_eq_refinement", "checker_eq_correct"],
        "EunoiaDirectFlat": ["flat_step_ext", "flat_run_ext", "flat_checker_ext", "checker_refinement", "checker_correct", "checker_b_refinement", "checker_b_correct", "checker_eq_refinement", "checker_eq_correct"],
        "EoStaged": ["compile_refinement"],
        "EoFuelLayers": ["fetch_make", "make_correct"],
        "EoCompiledPrograms": ["execute_correct"],
        "CpcStaged": ["execute_correct"],
        "CpcStagedEval": ["evaluate_correct"],
        "CpcStagedRules": ["run_rule_correct", "run_surface_correct", "derive_prepared_correct"],
        "EunoiaStaged": ["checker_refinement", "checker_correct", "checker_b_refinement", "checker_b_correct", "checker_eq_refinement", "checker_eq_correct"],
        "EunoiaProgramIndex": ["checker_refinement", "checker_correct", "checker_b_correct", "checker_eq_correct"],
        "EoNameIndex": ["lookup_insert", "lookup_from_list"],
        "EoIndexed": ["evaluate_indexed_refinement", "run_rule_refinement", "run_surface_refinement"],
        "EunoiaHelperCache": ["checker_refinement", "checker_correct",
                              "checker_b_refinement", "checker_b_correct",
                              "checker_eq_refinement", "checker_eq_correct"],
        "EoCheckedMemo": ["term_eqb_spec", "terms_eqb_spec", "key_eqb_equivalence", "cache_lookup_sound",
                          "evaluate_cached_refinement", "call_cached_refinement",
                          "entry_check_sound", "validate_entries_sound", "checked_evaluate_correct"],
        "EoRuleMemo": ["reference_factorization", "with_prepared_rule_ext",
                       "execute_using_ext", "run_rule_cached_refinement", "run_surface_cached_refinement"],
        "EunoiaMemo": ["gate_correct", "checker_correct", "checker_b_correct", "checker_eq_correct"],
        "EunoiaScopedAdapter": ["checker_correct", "checker_b_correct", "checker_eq_correct",
                                "scope_assumption_binding", "scope_eval_with_binding",
                                "cached_scope_eval_with_refinement", "prepared_scope_eval_with_refinement"],
        "EunoiaLocal": ["gate_correct", "array_clause_valid", "execute_array_binding"],
        "EunoiaLocalDirect": ["gate_correct"],
        "EunoiaCertificate": ["checker_tables", "checker_correct", "checker_b_correct", "checker_eq_correct"],
        "EunoiaTheory": ["units_exact", "units_valid", "negations_false",
                         "implication_correct", "checked_clause_correct",
                         "global_gate_correct", "gate_correct"],
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
        "EunoiaIntegerFacts": ["abs_laws", "min_laws", "max_laws", "sign_laws",
          "symbolic_positive_modulo", "symbolic_negative_modulo", "symbolic_zero_division",
          "known_quotient_divisor", "known_remainder_divisor"],
        "EunoiaDivision": ["positive_laws", "negative_laws", "zero_laws",
          "shift_laws", "positive_shift_laws", "negative_shift_laws",
          "positive_division_shift", "positive_modulo_shift",
          "negative_division_shift", "negative_modulo_shift",
          "nested_positive_law", "nested_positive_positive", "nested_negative_positive",
          "eqb_swap", "quotient_value", "remainder_value", "boolean_eq_true", "boolean_true_eq"],
        "EunoiaTactic": ["root_values_correct", "checker_correct", "checker_b_correct", "checker_eq_correct"],
    }.items():
        prefix = "SMTCoq.checker.eunoia." + module
        audit += ["--import", prefix]
        for name in names:
            audit += ["--theorem", prefix + "." + module + "." + name]
    for module, names in {
        "SMTCoq.checker.eunoia.CpcIndexed": ["program_lookup_correct", "derive_context_with_index_refinement", "derive_indexed_refinement", "derive_assuming_indexed_refinement"],
        "SMTCoq.checker.eunoia.CpcMemo": ["validate_context_sound", "derive_context_cached_refinement", "derive_checked_correct"],
        "SMTCoq.checker.eunoia.EoRuntime": ["nil_apply_refinement", "nil_list_apply_refinement",
                                         "resolve_nil_lazy_mode_refinement"],
        "SMTCoq.eunoia_runtime_profile.QueryRefinement": ["native_with_nils_refinement",
                                      "surface_in_with_refinement", "match_pattern_with_refinement"],
        "SMTCoq.eunoia_runtime_profile.SurfaceOutRefinement": ["surface_out_with_refinement"],
    }.items():
        audit += ["--import", module]
        for name in names:
            audit += ["--theorem", module + "." + name]
    audit += ["--import", "SMTCoq.utils.PArray", "--theorem", "SMTCoq.utils.PArray.IntOrderedType.compare_gt"]
    for test_module in ("EunoiaArrayTests", "EunoiaModelDagTests", "EunoiaLocalDirectTests", "EunoiaTheoryTests", "EunoiaCertificateTests"):
        test_import = "SMTCoq.checker.eunoia." + test_module
        audit += ["--import", test_import]
        for name in re.findall(r"^\s*(?:Lemma|Theorem|Example)\s+(\w+)",
                (ROOT / "theories/checker/eunoia" / (test_module + ".v")).read_text(), re.M):
            audit += ["--theorem", test_import + ("." + test_module if test_module in ("EunoiaArrayTests", "EunoiaLocalDirectTests", "EunoiaTheoryTests", "EunoiaCertificateTests") else "") + "." + name]
    for name in ("and_iff", "or_iff", "impl_iff", "iff_iff", "not_iff", "bool_true_iff"):
        audit += ["--import", "SMTCoq.tactics.preproc.EunoiaFrontend",
                  "--theorem", "SMTCoq.tactics.preproc.EunoiaFrontend.EunoiaFrontend." + name]
    public_modules = ("smtrocq_arrays", "smtrocq_integer_operations", "smtrocq", "eunoia_tactics", "eunoia_uf", "eunoia_uf_bool", "eunoia_lia", "eunoia_purification", "eunoia_integer_casts", "eunoia_division")
    for module in public_modules:
        public = "SMTCoq.tests." + module
        audit += ["--import", public]
        for name in re.findall(r"^\s*(?:Lemma|Theorem|Example)\s+(\w+)",
                               (ROOT / "unit-tests" / (module + ".v")).read_text(), re.M):
            audit += ["--theorem", public + "." + name]
    integration = "SMTCoq.eunoia_backend_tests.Lia"
    audit += ["--import", integration]
    for name in re.findall(r"^\s*(?:Lemma|Theorem|Example)\s+(\w+)",
            (ROOT / "src/eunoia_backend/tests/integration/Lia.v").read_text(), re.M):
        audit += ["--theorem", integration + "." + name]
    audit += ["--import", "SMTCoq.eunoia_backend_tests.Proof",
              "--theorem", "SMTCoq.eunoia_backend_tests.Proof.declared_hint_mutations"]
    audit += ["--import", "SMTCoq.checker.eunoia.CpcGenerated",
              "--theorem", "SMTCoq.checker.eunoia.CpcGenerated.cpc_canonicalize_correct",
              "--theorem", "SMTCoq.checker.eunoia.CpcGenerated.cpc_surface_correct"]
    audit += ["--import", "SMTCoq.checker.eunoia.EoSyntax",
              "--theorem", "SMTCoq.checker.eunoia.EoSyntax.term_eqb_refinement"]
    acceptance = "SMTCoq.eunoia_kernel_acceptance_probe.Controls"
    audit += ["--import", acceptance,
              "--theorem", acceptance + ".accepted",
              "--theorem", acceptance + ".rejected_before_callback",
              "--theorem", acceptance + ".transparent_data",
              "--theorem", acceptance + ".illtyped_data_rejected_before_callback"]
    commands = []
    summary = dict(passed=False, commands=commands)
    try:
        kernel = [wrapper, "rocq", "check", "-silent", *mappings,
                  "SMTCoq.eunoia_runtime_profile.QueryRefinement",
                  "SMTCoq.eunoia_runtime_profile.SurfaceOutRefinement",
                  "SMTCoq.checker.eunoia.EunoiaMemoTests",
                  "SMTCoq.checker.eunoia.EunoiaModelDagTests",
                  "SMTCoq.checker.eunoia.EunoiaArrayTests",
                  "SMTCoq.checker.eunoia.EunoiaLocalDirectTests",
                  "SMTCoq.checker.eunoia.EunoiaTheoryTests",
                  "SMTCoq.checker.eunoia.EunoiaCertificateTests",
                  "SMTCoq.checker.eunoia.EoCheckedMemoTests",
                  "SMTCoq.checker.eunoia.EunoiaHelperCache",
                  "SMTCoq.checker.eunoia.EunoiaProgramIndex",
                  "SMTCoq.checker.eunoia.EunoiaProgramIndexFlat",
                  "SMTCoq.checker.eunoia.EunoiaProgramIndexScoped",
                  "SMTCoq.checker.eunoia.EunoiaStagedTests",
                  "SMTCoq.checker.eunoia.EunoiaDirectTests",
                  "SMTCoq.checker.eunoia.EunoiaDirectScoped",
                  "SMTCoq.checker.eunoia.EunoiaDirectFlat",
                  "SMTCoq.checker.eunoia.EunoiaSpecializedTests",
                  "SMTCoq.checker.eunoia.EunoiaSpecializedScoped",
                  "SMTCoq.checker.eunoia.EunoiaSpecializedFlat",
                  "SMTCoq.checker.eunoia.EoNameIndexTests",
                  "SMTCoq.checker.eunoia.EunoiaProgramIndexTests",
                  "SMTCoq.checker.eunoia.EunoiaHelperCacheTests",
                  "SMTCoq.checker.eunoia.EunoiaScopedAdapter",
                  "SMTCoq.checker.eunoia.EunoiaIntegerEmbeddingTests",
                  integration, "SMTCoq.eunoia_backend_tests.Proof", acceptance,
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
