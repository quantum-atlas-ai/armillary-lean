"""Measure two subtrees of one p181 anchor on the same runner."""
import argparse
from array import array
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import subprocess
from time import monotonic

from render_reduced import BASE, ROOT, lean_list, packed, read_binary, table_source

WORK = Path(".lake/reduced")
OUT = WORK / "pilot"
CELL = 724


def index_tree(words):
    ends = array("I", [0]) * len(words)

    def visit(start):
        tag, arg = words[start], words[start+1]
        if tag in (0, 3):
            end = start + 2
        elif tag in (1, 4):
            end = start + 2 + (2 if tag == 4 else 1) * arg
        elif tag == 2:
            end = visit(visit(start + 2))
        else:
            raise ValueError(f"unknown opcode {tag}")
        ends[start] = end
        return end

    if visit(0) != len(words):
        raise ValueError("incomplete tree")
    return ends


def available_checkpoints(words, ends, address, base):
    matches = []

    def visit(start, chosen, path, mask):
        size = ends[start] - start
        if size < 12000:
            return
        if size <= 18000:
            matches.append((start, chosen, path, mask))
        elif words[start] == 2:
            col = words[start+1]
            new_path, new_mask = [col, *path], mask | (1 << col)
            visit(start + 2, [col, *chosen], new_path, new_mask)
            visit(ends[start + 2], chosen, new_path, new_mask)

    visit(0, [address], [address], base | (1 << address))
    if len(matches) < 4:
        raise ValueError("insufficient pilot checkpoints")
    return (matches[len(matches)//4], matches[3*len(matches)//4])


def render(sector, block, channel, base, words, ends, checkpoint, span, path):
    other = "Z" if sector == "X" else "X"
    scope = f"ArmillaryLean.CodeP181.Pilot{sector}"
    check, stab = f"{sector.lower()}Groups.get", f"{other.lower()}Groups.get"
    prior = f"(priorList 181 4 {block} {channel}).toFinset"
    prefix = f"Reduced.Excludes (certRows params {check}) (certRows params {stab}) 14"
    body = [
        "module",
        f"import {BASE}.CodeP181.WordsX\nimport {BASE}.CodeP181.WordsZ",
        "set_option maxRecDepth 32768\nset_option maxHeartbeats 0",
        f"namespace {scope}\n\nopen ArmillaryLean.Exclusion\nopen ArmillaryLean.Routed",
        f"theorem base_ok : {base:#x} = priorWord 181 4 {block} {channel} := by\n  decide +kernel",
    ]
    parts = 0

    def emit(start, chosen, branch, mask):
        nonlocal parts
        finish = ends[start]
        name = f"part{start}"
        selected, trail = lean_list(chosen), lean_list(branch)
        statement = (f"theorem {name} : {prefix}\n"
                     f"    ({selected} : List Nat).toFinset (({trail} : List Nat).toFinset ∪ {prior}) := by")
        if finish-start <= span or words[start] != 2:
            parts += 1
            body.append(f"def {name}Data : Program :=\n  {packed(words[start:finish])}")
            body.append(
                f"theorem {name}Ok : Reduced.run Words{sector}.word Words{other}.word "
                f"2172 8688 14\n    {selected} {mask:#x} {name}Data = true := by\n  decide +kernel")
            body.append(statement + f"\n  exact reduced_part Words{sector}.correct Words{other}.correct base_ok\n"
                                    f"    (by decide) (by decide) (by decide +kernel) {name}Ok")
        else:
            col = words[start+1]
            new_path, new_mask = [col, *branch], mask | (1 << col)
            yes = emit(start + 2, [col, *chosen], new_path, new_mask)
            no = emit(ends[start + 2], chosen, new_path, new_mask)
            body.append(statement + f"\n  apply Reduced.split_excludes {col}\n"
                                    f"  · simpa only [List.toFinset_cons, Finset.insert_union] using {yes}\n"
                                    f"  · simpa only [List.toFinset_cons, Finset.insert_union] using {no}")
        return name

    root = emit(*checkpoint)
    body.append(f"#print axioms {root}\n\nend {scope}")
    path.write_text("\n\n".join(body) + "\n")
    return parts


def run_file(file):
    proc = subprocess.run(
        ["/usr/bin/time", "-f", "elapsed=%e user=%U sys=%S peak_kib=%M",
         "lake", "--no-build", "lean", str(file)], text=True, capture_output=True)
    print(file.name, proc.stdout.strip(), proc.stderr.strip(), flush=True)
    proc.check_returncode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("sector", choices=["X", "Z"])
    parser.add_argument("anchor", type=int, choices=range(48))
    parser.add_argument("binary", type=Path)
    args = parser.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    for sector in "XZ":
        folder = ROOT / "CodeP181"
        folder.mkdir(parents=True, exist_ok=True)
        (folder / f"Words{sector}.lean").write_text(
            table_source("P181", sector, WORK / f"181-{sector}.rows"))
    subprocess.run(["lake", "build", *(f"+{BASE}.CodeP181.Words{sector}" for sector in "XZ")],
                   check=True)
    (words,) = read_binary(args.binary)
    ends = index_tree(words)
    block, channel = divmod(args.anchor, 4)
    address = block * CELL + channel
    base = ((1 << (block * CELL)) - 1) | sum(
        ((1 << channel) - 1) << (block * CELL + 4 * i) for i in range(181))
    checkpoints = available_checkpoints(words, ends, address, base)
    sizes = [ends[checkpoint[0]] - checkpoint[0] for checkpoint in checkpoints]
    order = (800, 1600) if (args.sector == "X") == (args.anchor == 0) else (1600, 800)
    for span in order:
        files = [OUT / f"Sample{span}P{i}.lean" for i in range(len(checkpoints))]
        parts = [render(args.sector, block, channel, base, words, ends, checkpoint, span, file)
                 for checkpoint, file in zip(checkpoints, files)]
        print(f"CASE {args.sector}{args.anchor:02} fragment={span} sizes={sizes} parts={parts}", flush=True)
        begin = monotonic()
        with ThreadPoolExecutor(max_workers=2) as pool:
            list(pool.map(run_file, files))
        elapsed = monotonic() - begin
        print(f"THROUGHPUT sector={args.sector} anchor={args.anchor} fragment={span} "
              f"words={sum(sizes)} seconds={elapsed:.2f} words_per_min={sum(sizes)*60/elapsed:.0f}",
              flush=True)


if __name__ == "__main__":
    main()
