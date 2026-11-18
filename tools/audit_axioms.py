"""Check the transitive axioms of the declarations in imported Armillary Lean modules."""

import argparse
from pathlib import Path
import re
import subprocess
from tempfile import TemporaryDirectory


AUDIT = """
set_option maxHeartbeats 0

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let mut checked := 0
  for modName in env.header.moduleNames, data in env.header.moduleData do
    unless (`ArmillaryLean).isPrefixOf modName do continue
    for name in data.constNames do
      unless (env.find? name).isSome do continue
      checked := checked + 1
      for axiomName in ← collectAxioms name do
        unless allowed.contains axiomName do
          throwError "Unexpected axiom {axiomName} in {name}"
  if checked == 0 then
    throwError "No Armillary Lean declarations audited"
  IO.println s!"Axiom audit passed for {checked} Armillary Lean declarations."
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("modules", nargs="*", default=["ArmillaryLean"])
    args = parser.parse_args()
    for module in args.modules:
        if not re.fullmatch(r"ArmillaryLean(?:\.[A-Za-z_][A-Za-z0-9_']*)*", module):
            parser.error(f"invalid Armillary Lean module {module!r}")
    imports = "\n".join(f"import all {module}" for module in args.modules or ["ArmillaryLean"])
    with TemporaryDirectory() as folder:
        probe = Path(folder) / "AxiomAudit.lean"
        probe.write_text(f"module\n\nmeta import Lean\n{imports}\n{AUDIT}", encoding="utf-8")
        subprocess.run(["lake", "--no-build", "lean", str(probe)], check=True)


if __name__ == "__main__":
    main()
