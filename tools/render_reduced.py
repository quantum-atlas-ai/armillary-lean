"""Render packed reduced certificates and their routed row tables as Lean modules."""

import argparse
import array
from pathlib import Path
import struct
import sys

from render8749 import render

BASE = "ArmillaryLean.Instances.ReducedProof"
SPECS = {"9053": (137, 3, 12), "P181": (181, 4, 14)}
ROOT = Path(*BASE.split("."))


def other(sector):
    return "Z" if sector == "X" else "X"


def update(file, source):
    if not file.exists() or file.read_text() != source:
        file.write_text(source)


def vector(items):
    return "#v[" + ", ".join(map(str, items)) + "]"


def table_source(code, sector, row_source):
    stations, channels, _ = SPECS[code]
    cell = stations * channels
    nr = 3 * cell
    rows = [list(map(int, line.split())) for line in row_source.read_text().splitlines()]
    if (len(rows) != nr or any(len(row) != 12 for row in rows)
            or any(c // cell != b for row in rows for b, c in enumerate(row))):
        raise ValueError("expected one routed column in each of the twelve blocks")
    values = [sum(1 << c for c in row) for row in rows]
    length = 1 << (nr - 1).bit_length()
    values += [0] * (length - nr)
    defs = []

    def emit_tree(items, tag):
        if len(items) == 1:
            return f"(.leaf {items[0]:#x})"
        left = emit_tree(items[::2], tag + "e")
        right = emit_tree(items[1::2], tag + "o")
        expr = f"(.fork {left} {right})"
        if len(items) >= 8:
            var = "tree" + tag
            defs.append(f"def {var} : Numeric.WordTree := {expr}")
            return var
        return expr

    emit_tree(values, "")
    zero = []
    for g in range(3):
        cells = []
        for block in range(12):
            coords = [divmod(rows[g * cell + j][block] % cell, channels) for j in range(channels)]
            cells.append(vector(f"({s}, {k})" for s, k in coords))
        zero.append("#v[" + ",\n    ".join(cells) + "]")
    zero_values = "#v[" + ",\n  ".join(zero) + "]"
    tables = "\n".join(defs)
    groups = sector.lower() + "Groups.get"
    return f"""module

public import ArmillaryLean.Instances.Data{code}
public import ArmillaryLean.Instances.ReducedRows

@[expose] public section
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace ArmillaryLean.Code{code}.Words{sector}

open ArmillaryLean.Exclusion
open ArmillaryLean.Routed
open Qatlib.Papers.Armillary26.Instances (armEff)

def zeroTable : Vector (Vector (Vector (Cell {stations} {channels}) {channels}) 12) 3 :=
  {zero_values}

def zeroRoute : ZeroTable {stations} {channels} := fun g b j => ((zeroTable.get g).get b).get j

/-- The station-zero entries agree with the source route. -/
theorem zero_correct : ∀ g b j, zeroRoute g b j = armEff params ({groups} g) b (0, j) := by
  decide +kernel

{tables}

def word (i : Nat) : Nat := if i < {nr} then tree.get i else 0

/-- The finite row table agrees with the fast reference word at every valid index. -/
theorem word_inside : ∀ i : Fin {nr}, word i.val = fastCertWord zeroRoute i.val := by
  decide +kernel

/-- The numeric table gives the routed rows in both directions. -/
theorem correct (i : Nat) : Numeric.Represents (word i) (certRows params {groups} i) := by
  have h : word i = fastCertWord zeroRoute i := by
    by_cases hi : i < {nr}
    · exact word_inside ⟨i, hi⟩
    · simp only [word, fastCertWord, ite_eq_right hi, dite_eq_right hi]
  rw [h, fastCertWord_eq params {groups} zeroRoute zero_correct]
  exact certWord_rep params {groups} i

end ArmillaryLean.Code{code}.Words{sector}
"""


def read_binary(path):
    with path.open("rb") as f:
        while header := f.read(8):
            count, = struct.unpack("<Q", header)
            words = array.array("H")
            words.fromfile(f, count)
            if sys.byteorder != "little":
                words.byteswap()
            yield words


def split_points(words):
    points = {}
    def parse(pos):
        tag = words[pos]
        if tag in (0, 3):
            return pos + 2
        if tag == 1:
            return pos + 2 + words[pos + 1]
        if tag == 4:
            return pos + 2 + 2 * words[pos + 1]
        if tag == 2:
            mid = parse(pos + 2)
            points[pos] = mid
            return parse(mid)
        raise ValueError(f"invalid opcode {tag} at {pos}")
    if parse(0) != len(words):
        raise ValueError("the words must contain exactly one complete program")
    return points


def lean_list(items):
    return "[" + ", ".join(map(str, items)) + "]"


def packed(words):
    chunks = []
    for i in range(0, len(words), 36):
        group = words[i:i+36]
        if any(w >= 16384 for w in group):
            raise ValueError("word out of range")
        payload = sum(w << (14 * j) for j, w in enumerate(group))
        chunks.append(f"(.chunk {len(group)} {payload:#x})")
    return render(chunks, 0, len(chunks))


def module_source(code, scope, imports, body):
    loading = "".join(f"public import {m}\n" for m in imports)
    return f"""module

{loading}
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace ArmillaryLean.Code{code}.{scope}

open ArmillaryLean.Exclusion
open ArmillaryLean.Routed

{body}

end ArmillaryLean.Code{code}.{scope}
"""


def render_anchor(code, sector, anchor, words, fragment, page, merge_pages=True):
    p, q, budget = SPECS[code]
    block, chan = divmod(anchor, q)
    size = p * q
    addr = block * size + chan
    base = ((1 << (block * size)) - 1) | sum(
        ((1 << chan) - 1) << ((block * size) + q * i) for i in range(p))
    name = f"{sector}{anchor:02d}"
    folder = ROOT / f"Code{code}" / name
    folder.mkdir(parents=True, exist_ok=True)
    prefix = f"{BASE}.Code{code}.{name}"
    opp = f"{sector.lower()}Groups.get"
    stab = f"{other(sector).lower()}Groups.get"
    desc = f"Reduced.Excludes (certRows params {opp}) (certRows params {stab}) {budget}"
    prior = f"(priorList {p} {q} {block} {chan}).toFinset"
    imports = [f"{BASE}.Code{code}.Words{s}" for s in (sector, other(sector))]
    points = split_points(words)
    pages = []
    page_parts = []
    page_weight = 0
    page_name = None

    update(folder / "Base.lean", module_source(code, name, imports, f"""
/-- The earlier-rank mask is exactly the mask defined from numeric coordinates. -/
public theorem base_ok : {base:#x} = priorWord {p} {q} {block} {chan} := by
  decide +kernel
"""))

    def flush_page():
        nonlocal page_weight
        if page_parts:
            pages.append(f"{prefix}.{page_name}")
            update(folder / f"{page_name}.lean", module_source(code, name,
                [f"{prefix}.Base"], "\n\n".join(page_parts)))
            page_parts.clear()
            page_weight = 0

    def group(start, end, chosen, path, mask, declarations, can_page, exported=False):
        nonlocal page_weight, page_name
        label = f"part{start}"
        if can_page and end - start <= page:
            if page_weight + end - start > page:
                flush_page()
            if not page_parts:
                page_name = f"Page{start}"
            group(start, end, chosen, path, mask, page_parts, False, True)
            page_weight += end - start
            if not merge_pages:
                flush_page()
            return label
        chosen_str, path_str = lean_list(chosen), lean_list(path)
        visibility = "public " if exported else ""
        statement = f"""{visibility}theorem {label} : {desc}
    ({chosen_str} : List Nat).toFinset (({path_str} : List Nat).toFinset ∪ {prior}) := by
"""
        if end - start <= fragment or start not in points:
            declarations.append(f"def {label}Data : Program :=\n  {packed(words[start:end])}")
            declarations.append(
                f"theorem {label}Ok : Reduced.run Words{sector}.word Words{other(sector)}.word "
                f"{3*size} {12*size} {budget}\n    {chosen_str} {mask:#x} {label}Data = true := by\n"
                "  decide +kernel"
            )
            declarations.append(statement + (
                f"  exact reduced_part Words{sector}.correct Words{other(sector)}.correct base_ok\n"
                f"    (by decide) (by decide) (by decide +kernel) {label}Ok"
            ))
        else:
            c = words[start+1]
            mid = points[start]
            next_path, next_mask = [c, *path], mask | (1 << c)
            yes = group(start + 2, mid, [c, *chosen], next_path, next_mask, declarations, can_page)
            no = group(mid, end, chosen, next_path, next_mask, declarations, can_page)
            declarations.append(statement + f"""  apply Reduced.split_excludes {c}
  · simpa only [List.toFinset_cons, Finset.insert_union] using {yes}
  · simpa only [List.toFinset_cons, Finset.insert_union] using {no}""")
        return label

    pieces = []
    root = group(0, len(words), [addr], [addr], base | (1 << addr), pieces, len(words) > page)
    flush_page()
    pieces.append(f"""/-- This checked program excludes the physical minimum-rank anchor. -/
public theorem verified (s : Finset (Coord {p} {q})) (ha : ({block}, (0, {chan})) ∈ s)
    (hm : ∀ v ∈ s, anchorRank (p := {p}) (q := {q}) ({block}, (0, {chan})) ≤ anchorRank v)
    (hz : ZeroSyndrome (neighbors params {opp}) s) (hw : s.card ≤ {budget})
    (ho : ∀ r, (s ∩ neighbors params {stab} r).card ≤ 6) : False := by
  refine reduced_root params {opp} {stab} {block} {chan} {budget} ?_ s ha hm hz hw ho
  exact {root}
""")
    update(folder.with_suffix(".lean"), module_source(code, name,
        [f"{prefix}.Base", *pages], "\n\n".join(pieces)))
    return [f"{prefix}.Base", *pages, prefix]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("code", choices=SPECS)
    parser.add_argument("sector", choices=("X", "Z"))
    parser.add_argument("--rows", type=Path)
    parser.add_argument("--programs", type=Path)
    parser.add_argument("--begin", type=int, default=0)
    parser.add_argument("--anchors", type=int, nargs="*")
    parser.add_argument("--fragment-words", type=int, default=800)
    parser.add_argument("--page-words", type=int, default=20000)
    parser.add_argument("--separate-pages", action="store_true")
    args = parser.parse_args()
    if (args.rows is None) == (args.programs is None):
        parser.error("provide either --rows or --programs")
    if not 2 <= args.fragment_words <= args.page_words:
        parser.error("invalid fragment or page size")
    if args.rows is not None:
        destination = ROOT / f"Code{args.code}"
        destination.mkdir(parents=True, exist_ok=True)
        update(destination / f"Words{args.sector}.lean", table_source(args.code, args.sector, args.rows))
        print(f"{BASE}.Code{args.code}.Words{args.sector}")
        return
    anchors = None if args.anchors is None else set(args.anchors)
    for anchor, words in enumerate(read_binary(args.programs), args.begin):
        if anchors is None or anchor in anchors:
            for module in render_anchor(args.code, args.sector, anchor, words,
                                        args.fragment_words, args.page_words, not args.separate_pages):
                print(module)


if __name__ == "__main__":
    main()
