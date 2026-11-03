#!/usr/bin/env python3
"""Temporarily record table slots around each witness call in Rocq Profile.

Only the assigned backend is changed. Restore and rebuild after measurement;
the saved and instrumented hashes protect against overwriting later edits.
The arrays used for counting are temporary: these instrumented timings must
not be compared with uninstrumented production timings.
"""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TARGET = ROOT / "src/eunoia_backend/eunoiaBackend.ml"
BEFORE = "    let evidence st syntax_cs cs c =\n"
AFTER = "      checked_steps := (st,syntax_cs,cs,c,w)::!checked_steps;\n"
PROBE = '''      let sizes phase =
        NewProfile.profile "Eunoia.witness_tables" ~args:(fun () -> [
          "step", `String st.E.name; "phase", `String phase;
          "atom_slots", `Intlit (string_of_int (Array.length (Atom.to_array t.atoms () (fun _ -> ()))));
          "form_slots", `Intlit (string_of_int (Array.length (Form.pform_tbl t.forms)))])
          (fun () -> ()) () in
      sizes "before";
'''
INPUT = '''let record_checker_input computation =
  NewProfile.profile "Eunoia.checker_input" ~args:(fun () -> [
    "expression", `String (Pp.string_of_ppcmds (Constr.debug_print computation))])
    (fun () -> computation) ()

'''


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("install", "restore"))
    parser.add_argument("--backup", type=Path, required=True)
    args = parser.parse_args()
    backup = args.backup.resolve()
    if backup == ROOT or ROOT in backup.parents:
        parser.error("backup must be outside the checkout")
    if args.action == "install":
        data = TARGET.read_bytes()
        text = data.decode()
        if text.count(BEFORE) != 1 or text.count(AFTER) != 1:
            parser.error("backend anchors changed")
        modified = text.replace(BEFORE, BEFORE + PROBE).replace(AFTER, '      sizes "after";\n' + AFTER).encode()
        instrumented = modified.decode()
        anchor = "let refutation env sigma p =\n"
        if instrumented.count(anchor) != 1:
            parser.error("refutation anchor changed")
        instrumented = instrumented.replace(anchor, INPUT + anchor)
        call = '(C.call (p.checker_api "checker") args)'
        if instrumented.count(call) != 1:
            parser.error("refutation checker anchor changed")
        instrumented = instrumented.replace(call, '(record_checker_input ' + call + ')')
        candidate = "let with_checked_acceptance p computation use =\n"
        if candidate in instrumented:
            instrumented = instrumented.replace(candidate, candidate + "  let computation = record_checker_input computation in\n")
        else:
            call = '(C.call (prepared.checker_api name) args)'
            if instrumented.count(call) != 1:
                parser.error("tactic checker anchor changed")
            instrumented = instrumented.replace(call, '(record_checker_input ' + call + ')')
        modified = instrumented.encode()
        backup.mkdir(parents=True, exist_ok=False)
        (backup / "original.ml").write_bytes(data)
        (backup / "manifest.json").write_text(json.dumps(dict(
            target=str(TARGET), original_sha256=digest(data), modified_sha256=digest(modified)), indent=2) + "\n")
        TARGET.write_bytes(modified)
    else:
        manifest = json.loads((backup / "manifest.json").read_text())
        original = (backup / "original.ml").read_bytes()
        if (manifest["target"] != str(TARGET) or digest(original) != manifest["original_sha256"]
                or digest(TARGET.read_bytes()) != manifest["modified_sha256"]):
            parser.error("source/backup changed; refusing to restore")
        TARGET.write_bytes(original)


if __name__ == "__main__":
    main()
