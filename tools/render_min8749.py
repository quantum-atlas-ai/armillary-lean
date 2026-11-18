"""Render minimum-rank candidate trees as proofs from numeric checkpoints."""

import argparse
from pathlib import Path

from render8749 import packed_chunks, render, split_points_of


def proof_source(words, checks, budget, anchor, limit, pages=None, page_limit=None):
    sector = 0 if checks == "X" else 1
    block, channel = divmod(anchor, 3)
    address = 303 * block + channel
    prefix = (1 << (303 * block)) - 1
    earlier_channels = (((1 << 303) - 1) // 7) * ((1 << channel) - 1)
    earlier = prefix | (earlier_channels << (303 * block))
    split = split_points_of(words)
    namespace = f"Min{checks}{anchor:02d}"
    declarations = [f"namespace {namespace}"]

    def fragment(start, end, chosen, path, marked, declarations, paging, exported=False):
        name = f"part{start}"
        if paging and end - start <= page_limit:
            page = [f"namespace {namespace}"]
            fragment(start, end, chosen, path, marked, page, False, exported=True)
            page.append(f"end {namespace}")
            pages[start] = "\n\n".join(page)
            return name
        visibility = "public " if exported else ""
        statement = (
            f"{visibility}theorem {name} : Excluded (numericRows {sector}) {budget}\n"
            f"    ({chosen} : List Nat).toFinset (checkpointSet {block} {channel} {path}) := by\n"
        )
        if end - start <= limit or start not in split:
            chunks = packed_chunks(words[start:end])
            declarations.append(f"def {name}Data : Program :=\n  {render(chunks, 0, len(chunks))}")
            declarations.append(
                f"theorem {name}Ok : Numeric.run Words{checks}.word 909 3636 {budget}\n"
                f"    {chosen} {marked:#x} {name}Data = true := by\n  decide +kernel"
            )
            declarations.append(
                statement + f"  exact checkedNumericPart Words{checks}.correct (by decide) (by decide)\n"
                f"    (by decide +kernel) {name}Ok"
            )
        else:
            c = words[start + 1]
            mid = split[start]
            next_path = [c, *path]
            next_word = marked | (1 << c)
            yes = fragment(start + 2, mid, [c, *chosen], next_path, next_word, declarations, paging)
            no = fragment(mid, end, chosen, next_path, next_word, declarations, paging)
            declarations.append(
                statement + f"  apply split_excluded {c}\n"
                f"  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using {yes}\n"
                f"  · simpa only [checkpointSet, List.toFinset_cons, Finset.insert_union] using {no}"
            )
        return name

    paging = pages is not None and len(words) > page_limit
    name = fragment(0, len(words), [address], [address], earlier | (1 << address), declarations, paging)
    declarations.append(f'''/-- The checked exclusion of this physical minimum-rank anchor. -/
public theorem verified (s : Finset Coord) (ha : ({block}, (0, {channel})) ∈ s)
    (hm : ∀ v ∈ s, anchorRank ({block}, (0, {channel})) ≤ anchorRank v)
    (hz : ZeroSyndrome (neighbors (retained {sector})) s) (hw : s.card ≤ {budget}) : False := by
  apply min_from_root (b := {block}) (j := {channel}) _ ha hm hz hw
  exact {name}

#print axioms verified

end Min{checks}{anchor:02d}''')
    return "\n\n".join(declarations)


def module_source(proof, checks, imports=()):
    additional = "".join(f"public import {name}\n" for name in imports)
    return f'''module

public import ArmillaryLean.Instances.MinNumeric8749
public import ArmillaryLean.Instances.WordData8749.{checks}
{additional}
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace ArmillaryLean.Code8749

open ArmillaryLean.Exclusion

''' + '\n\n'.join(proof) + '\n\nend ArmillaryLean.Code8749\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("words", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--checks", choices=("X", "Z"), required=True)
    parser.add_argument("--budget", type=int, choices=range(1, 11), required=True)
    parser.add_argument("--begin", type=int, required=True)
    parser.add_argument("--fragment-words", type=int, default=500)
    args = parser.parse_args()
    if args.fragment_words < 2:
        parser.error("expected a fragment limit of at least two words")
    with args.words.open() as programs:
        proof = []
        for anchor, line in enumerate(programs, args.begin):
            words = list(map(int, line.split()))
            if not 0 <= anchor < 36 or not words or any(not 0 <= w < 4096 for w in words):
                parser.error(f"invalid word data for anchor {anchor}")
            proof.append(proof_source(words, args.checks, args.budget, anchor, args.fragment_words))
    if not proof:
        parser.error("expected at least one program")
    args.output.write_text(module_source(proof, args.checks))


if __name__ == "__main__":
    main()
