#!/usr/bin/env python3
"""Recompile saved focused sources together, audit, and recursively kernel-check.

Aggregation gives each theorem a unique name so dependencies need checking only
once. It reruns the tactics, including every private helper check. It changes
no theorem, fuel, solver limit, or proof step. Profiles are removed from this
validation-only compilation; Time tactic and Time Qed remain.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re

spec = importlib.util.spec_from_file_location("reuse", Path(__file__).with_name("run.py"))
reuse = importlib.util.module_from_spec(spec)
spec.loader.exec_module(reuse)


def hashes(paths):
    return {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--profile-dir", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    if output == reuse.ROOT or reuse.ROOT in output.parents or '"' in str(output) or "\n" in str(output):
        parser.error("output must be external and contain no quotes or newlines")
    output.mkdir(parents=True, exist_ok=False)
    profile_dir = args.profile_dir.resolve()
    cases = [r["case"] for r in json.loads((profile_dir / "results.json").read_text())
             if r["repeat"] == 1 and r["checked"]]
    if not cases:
        parser.error("no checked sources")
    sources = []
    theorems = []
    helpers = []
    for case in cases:
        source = (profile_dir / (case + "-1") / "Case.v").read_text()
        source = re.sub(r'^Profile "[^"\n]+" (Time .+)$', r'\1', source, flags=re.M)
        name = "checked_" + case
        sources.append(source.replace("profile_result", name))
        theorems.append(name)
        helpers.append(name)
    controls = profile_dir / "controls/Controls.v"
    if controls.is_file():
        sources.append(controls.read_text())
        theorems += list(reuse.CONTROL_THEOREMS)
        helpers += list(reuse.CONTROL_HELPERS)
    source = output / "Validation.v"
    source.write_text("\n".join(sources))
    flags = [*reuse.profile.loadpath(), "-Q", str(output), "EunoiaProofReuseValidation"]
    results = []
    for name, command in [
        ("build", [reuse.WRAPPER, "dune", "build", "-j2", "src/smtcoq.cmxs",
                   "src/eunoia_backend/eunoia_backend.cmxs",
                   "src/eunoia_backend/tests/integration/backend_test_plugin.cmxs"]),
        ("compiler", [reuse.WRAPPER, "dune", "exec", "-j2", "--", "rocq", "c", "-q", *flags,
                      "-I", str(reuse.ROOT / "_build/install/default/lib"), str(source)]),
    ]:
        directory = output / name
        directory.mkdir()
        result = reuse.execute(command, directory, 120)
        results.append(result)
        if result["exit_code"] or result["timeout"]:
            reuse.profile.write_json(output / "status.json", dict(passed=False, results=results))
            return 1
    auditdir = output / "audit"
    auditdir.mkdir()
    command = ["python3", "-B", str(reuse.ROOT / "tools/audit-eunoia-assumptions.py"),
               "--import", "EunoiaProofReuseValidation.Validation", "--loadpath", str(output),
               "EunoiaProofReuseValidation", "--output-dir", str(auditdir)]
    for theorem in theorems:
        command += ["--theorem", theorem]
    audit = reuse.execute(command, auditdir, 120)
    results.append(audit)
    failed = bool(audit["exit_code"]) or audit["timeout"]
    failed |= bool(reuse.audit_helpers(output / "helpers", "EunoiaProofReuseValidation.Validation",
                                       helpers, flags, 120))
    artifacts = list((reuse.ROOT / "_build/default/theories").rglob("*.vo")) + [source.with_suffix(".vo")]
    before = hashes(artifacts)
    kerneldir = output / "kernel"
    kerneldir.mkdir()
    kernel = reuse.execute([reuse.WRAPPER, "rocq", "check", "-silent", "-bytecode-compiler", "yes",
                            *flags, "EunoiaProofReuseValidation.Validation"], kerneldir, 120)
    results.append(kernel)
    failed |= bool(kernel["exit_code"]) or kernel["timeout"]
    after = hashes(artifacts)
    failed |= before != after
    reuse.profile.write_json(output / "status.json", dict(
        passed=not failed, results=results, theorems=theorems, helper_bodies=helpers,
        source_sha256=hashes([source, reuse.ROOT / "src/eunoia_backend/eunoiaBackend.ml"]),
        artifact_sha256_before=before, artifact_sha256_after=after))
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
