#!/usr/bin/env python3
"""Temporary, fail-closed profiling of the Eunoia marshaling boundary.

Use only in an idle, isolated checkout. Restore before committing production
code. The original bytes and both hashes are retained outside the checkout.
"""

import argparse
import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "src/eunoia_backend/eunoiaRocq.ml"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def instrument(source):
    def replace(old, new):
        nonlocal source
        if source.count(old) != 1:
            raise ValueError(f"expected exactly one instrumentation anchor: {old!r}")
        source = source.replace(old, new)

    replace("let global name =", "let profile_global name =")
    replace("let call name args =", """let global name =
  NewProfile.profile "Eunoia.global" (fun () -> profile_global name) ()
let profile_vm env tm ty =
  let h,_ = R.decompose_app_list tm in
  let name = match Constr.kind h with
    | Constr.Const (c,_) -> Names.Constant.to_string c
    | _ -> "nonconstant" in
  NewProfile.profile ("Eunoia.cbv_vm:" ^ name)
    (fun () -> R.cbv_vm env tm ty) ()
let call name args =""")
    replace("let string s =", "let profile_string s =")
    replace("let syntax =", """let string s =
  NewProfile.profile "Eunoia.string" (fun () -> profile_string s) ()
let syntax =""")
    replace("let term_list xs =", """let profile_term = term
let term t = NewProfile.profile "Eunoia.term" (fun () -> profile_term t) ()
let term_list xs =""")
    replace("let compute_term_option env tm =", """let profile_decode_term = decode_term
let decode_term t =
  NewProfile.profile "Eunoia.decode_term" (fun () -> profile_decode_term t) ()
let compute_term_option env tm =""")
    replace("let v = R.cbv_vm env tm ty in", "let v = profile_vm env tm ty in")
    replace("(R.cbv_vm env inventory list_ty)", "(profile_vm env inventory list_ty)")
    replace("R.vm_conv Conversion.CUMUL env computation (Lazy.force CoqTerms.ctrue)",
            "NewProfile.profile \"Eunoia.checked_true\" (fun () ->\n"
            "    R.vm_conv Conversion.CUMUL env computation (Lazy.force CoqTerms.ctrue)) ()")
    return source


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("install", "restore"))
    parser.add_argument("--backup", type=Path, required=True,
                        help="new directory outside the checkout for original bytes and hashes")
    args = parser.parse_args()
    backup = args.backup.resolve()
    if backup == ROOT or ROOT in backup.parents:
        parser.error("backup must be outside the checkout")
    if args.action == "install":
        original = SOURCE.read_bytes()
        modified = instrument(original.decode()).encode()
        backup.mkdir(parents=True, exist_ok=False)
        (backup / "original.ml").write_bytes(original)
        (backup / "instrumented.ml").write_bytes(modified)
        (backup / "manifest.json").write_text(json.dumps({
            "source": str(SOURCE), "original_sha256": digest(original),
            "instrumented_sha256": digest(modified)}, indent=2) + "\n")
        SOURCE.write_bytes(modified)
    else:
        manifest = json.loads((backup / "manifest.json").read_text())
        original = (backup / "original.ml").read_bytes()
        if (manifest["source"] != str(SOURCE)
                or digest(original) != manifest["original_sha256"]
                or digest(SOURCE.read_bytes()) != manifest["instrumented_sha256"]):
            parser.error("source or backup changed; refusing to overwrite")
        SOURCE.write_bytes(original)
    print(f"{args.action}: {SOURCE}")


if __name__ == "__main__":
    main()
