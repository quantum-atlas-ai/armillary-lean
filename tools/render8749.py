"""Render candidate search words as a bounded-depth kernel-checkable Lean file."""

import argparse
from pathlib import Path


def packed_chunks(words):
    chunks = []
    for start in range(0, len(words), 42):
        group = words[start : start + 42]
        payload = sum(word << (12 * index) for index, word in enumerate(group))
        chunks.append(f"(.chunk {len(group)} {payload:#x})")
    return chunks


def render(chunks, start, end, indent="  "):
    if end - start == 1:
        return chunks[start]
    mid = (start + end) // 2
    child = indent + "  "
    left = render(chunks, start, mid, child)
    right = render(chunks, mid, end, child)
    return f"(.append\n{child}{left}\n{child}{right})"


def column(address):
    block, cell = divmod(address, 303)
    station, channel = divmod(cell, 3)
    return f"({block}, ({station}, {channel}))"


def fragments(words, sector, budget, anchor, limit):
    split_points = {}

    def endpoint(start):
        opcode, argument = words[start : start + 2]
        if opcode == 0:
            return start + 2
        if opcode == 1:
            return start + 2 + argument
        if opcode != 2 or argument >= 3636:
            raise ValueError("invalid split instruction")
        right = endpoint(start + 2)
        end = endpoint(right)
        split_points[start] = right
        return end

    if endpoint(0) != len(words):
        raise ValueError("expected one full tree")
    declarations = []

    def emit(start, end, selected, decided):
        name = f"part{start}"
        chosen = "[" + ", ".join(map(column, selected)) + "]"
        marked = "[" + ", ".join(map(column, decided)) + "]"
        statement = (
            f"theorem {name} : Excluded (neighbors (retained {sector})) {budget}\n"
            f"    ({chosen} : List Coord).toFinset ({marked} : List Coord).toFinset := by\n"
        )
        if end - start <= limit or start not in split_points:
            chunks = packed_chunks(words[start:end])
            declarations.append(f"def {name}Data : Program :=\n  {render(chunks, 0, len(chunks))}\n")
            declarations.append(
                f"theorem {name}Ok : checkFragment {sector} {budget} {chosen} {marked} "
                f"{name}Data = true := by\n  decide +kernel\n"
            )
            declarations.append(statement + f"  exact checkedFragment (by decide) (by decide) {name}Ok\n")
        else:
            next_col = words[start + 1]
            right_start = split_points[start]
            new_marked = [next_col, *decided]
            left = emit(start + 2, right_start, [next_col, *selected], new_marked)
            right = emit(right_start, end, selected, new_marked)
            declarations.append(
                statement + f"  apply split_excluded {column(next_col)}\n"
                f"  · simpa only [List.toFinset_cons] using {left}\n"
                f"  · simpa only [List.toFinset_cons] using {right}\n"
            )
        return name

    address = (anchor // 3) * 303 + anchor % 3
    name = emit(0, len(words), [address], [address])
    return "\n".join(declarations) + f"\n#print axioms {name}\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("words", type=Path, help="one search-program word stream")
    parser.add_argument("output", type=Path)
    parser.add_argument("--checks", choices=("X", "Z"), required=True)
    parser.add_argument("--anchor", type=int, choices=range(36), required=True)
    parser.add_argument("--budget", type=int, choices=range(1, 11), required=True)
    parser.add_argument("--checker", choices=("masked", "finset"), default="masked")
    parser.add_argument("--fragment-words", type=int, help="split proof reduction into small subtrees")
    args = parser.parse_args()
    words = [int(word) for word in args.words.read_text().split()]
    if not words or any(not 0 <= word < 4096 for word in words):
        parser.error("the input must contain a nonempty stream of twelve-bit words")
    sector = 0 if args.checks == "X" else 1
    prefix = '''module

import ArmillaryLean.Instances.Anchor8749

open ArmillaryLean.Code8749
open ArmillaryLean.Exclusion

set_option maxRecDepth 8192
set_option maxHeartbeats 0

'''
    if args.fragment_words is not None:
        if args.fragment_words < 2 or args.checker != "masked":
            parser.error("fragmented checking requires the masked checker and a limit of at least two words")
        args.output.write_text(prefix + fragments(words, sector, args.budget, args.anchor, args.fragment_words))
        return
    chunks = packed_chunks(words)
    block, channel = divmod(args.anchor, 3)
    check = "checkMasked" if args.checker == "masked" else "checkAnchor"
    args.output.write_text(prefix + f'''def candidate : Program :=
  {render(chunks, 0, len(chunks))}

theorem candidate_checked : {check} {sector} {args.budget} {block} {channel} candidate = true := by
  decide +kernel

#print axioms candidate_checked
''')


if __name__ == "__main__":
    main()
