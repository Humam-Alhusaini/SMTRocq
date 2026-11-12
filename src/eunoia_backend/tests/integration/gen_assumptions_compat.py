"""Select the typed assumption-printer API of the active Rocq compiler."""
from pathlib import Path
import re
import subprocess
import sys

version = subprocess.check_output(["rocq", "--version"], text=True)
match = re.search(r"version\s+(\d+)\.(\d+)", version)
if not match:
    raise SystemExit("Cannot identify the active Rocq assumption API")
modern = tuple(map(int, match.groups())) >= (9, 3)
binding = "theory, assumptions" if modern else "assumptions"
arguments = "theory assumptions" if modern else "assumptions"
Path(sys.argv[1]).write_text(f'''(* Generated typed compatibility for the active Rocq toolchain. *)
let print opaque_access refs =
  let {binding} = Assumptions.assumptions opaque_access TransparentState.full refs in
  let env = Global.env () in
  Printer.pr_assumptionset env (Evd.from_env env) {arguments}
''')
