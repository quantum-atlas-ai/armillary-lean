"""Generate a lookup table whose words Lean checks against the routed rows."""

import argparse
from pathlib import Path


def declarations(words):
    result = []

    def emit(page, name):
        if len(page) == 1:
            return f"(.leaf {page[0]:#x})"
        even = emit(page[::2], name + "e")
        odd = emit(page[1::2], name + "o")
        value = f"(.fork {even} {odd})"
        if len(page) < 8:
            return value
        result.append(f"def {name} : Numeric.WordTree := {value}")
        return name

    emit(words, "pages")
    return "\n".join(result)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("rows", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--checks", choices=("X", "Z"), required=True)
    args = parser.parse_args()
    rows = [set(map(int, line.split())) for line in args.rows.read_text().splitlines()]
    if len(rows) != 909 or any(len(row) != 12 or min(row) < 0 or max(row) >= 3636 for row in rows):
        parser.error("expected 909 rows with twelve column addresses each")
    words = [sum(1 << col for col in row) for row in rows]
    words.extend([0] * (1024 - len(words)))
    label = args.checks
    sector = 0 if label == "X" else 1
    args.output.write_text(f'''module

public import ArmillaryLean.Instances.Numeric8749

@[expose] public section

namespace ArmillaryLean.Code8749.Words{label}

open ArmillaryLean.Exclusion

{declarations(words)}

/-- Cached numeric words for the routed check rows. -/
def word (address : Nat) : Nat := if address < 909 then pages.get address else 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
/-- All cached words agree with their routed reference on valid addresses. -/
private theorem checked : ∀ i : Fin 909, word i.val = referenceWord {sector} i.val := by
  decide +kernel

/-- Every word is justified by the routed source, including invalid addresses. -/
theorem correct : CorrectWords {sector} word := by
  intro n
  by_cases h : n < 909
  · exact checked ⟨n, h⟩
  · simp [word, referenceWord, decodeRow, h]

end ArmillaryLean.Code8749.Words{label}
''')


if __name__ == "__main__":
    main()
