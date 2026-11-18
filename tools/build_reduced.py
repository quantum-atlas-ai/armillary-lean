"""Build routed reduced certificates and assemble checked exact distances."""

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import os
from pathlib import Path
import subprocess

from render_reduced import BASE, ROOT, SPECS, read_binary, render_anchor, table_source, update


def assemble_source(code, sectors, channels):
    module = f"{BASE}.Code{code}"
    imports = "\n".join(
        f"public import {module}.{sector}{anchor:02d}"
        for sector in sectors for anchor in range(12 * channels)
    )
    _, _, budget = SPECS[code]
    families = []
    for sector in sectors:
        stab, opposite = ("z", "x") if sector == "X" else ("x", "z")
        cases = "\n".join(f"  · exact {sector}{i:02d}.verified s ha hm hz hw ho" for i in range(12 * channels))
        families.append(f"""/-- All checked reduced anchors for the {sector} check matrix. -/
theorem all{sector} : ReducedAnchors params {stab}Groups.get {opposite}Groups.get {budget} := by
  intro b j s ha hm hz hw ho
  fin_cases b <;> fin_cases j
{cases}""")
    if code == "9053":
        assembly = "distance_eq_fourteen_of_x allX"
        required = "ArmillaryLean.Instances.Swap9053"
        name, distance = "fourteen", 14
    else:
        assembly = "distance_eq_sixteen_of_anchors allZ allX"
        required = "ArmillaryLean.Instances.ReducedDistances"
        name, distance = "sixteen", 16
    proofs = "\n\n".join(families)
    return f"""module

public import {required}
{imports}
import Mathlib.Tactic.FinCases

@[expose] public section
set_option maxRecDepth 8192

namespace ArmillaryLean.Code{code}

open ArmillaryLean.Routed (ReducedAnchors)
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode (cssDistance)

{proofs}

/-- The exact CSS distance of the concrete routed instance. -/
theorem distance_eq_{name} : cssDistance code = {distance} := {assembly}

#print axioms distance_eq_{name}

end ArmillaryLean.Code{code}
"""


def build(name, timeout, logs, targets=None):
    log = logs / (name + ".log")
    targets = [name] if targets is None else targets
    with log.open("w") as output:
        try:
            status = subprocess.run(
                ["lake", "build", *(f"+{target}" for target in targets)],
                env={**os.environ, "LAKE_ARTIFACT_CACHE": "true"},
                stdout=output,
                stderr=subprocess.STDOUT,
                timeout=timeout,
                check=False,
            ).returncode
        except subprocess.TimeoutExpired:
            status = 124
    print(name, status, log, flush=True)
    return status == 0


def stage(names, jobs, timeout, logs):
    if not names:
        return True
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        pending = [pool.submit(build, name, timeout, logs) for name in names]
        results = [future.result() for future in as_completed(pending)]
    return all(results)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("code", choices=SPECS)
    parser.add_argument("--work", type=Path, default=Path(".lake/reduced"))
    parser.add_argument("--begin", type=int, default=0, help="anchor of the first program in each binary")
    parser.add_argument("--anchors", type=int, nargs="+", help="check only this subset")
    parser.add_argument("--sector", choices=("X", "Z"), help="check only this sector")
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--timeout", type=int, default=900)
    parser.add_argument("--fragment-words", type=int, default=800)
    parser.add_argument("--page-words", type=int, default=20000)
    parser.add_argument("--separate-pages", action="store_true")
    parser.add_argument("--generate-only", action="store_true")
    args = parser.parse_args()
    p, q, _ = SPECS[args.code]
    anchors = set(range(12 * q) if args.anchors is None else args.anchors)
    if (not args.jobs > 0 or not args.timeout > 0 or not 0 <= args.begin <= min(anchors)
            or max(anchors) >= 12 * q or not 2 <= args.fragment_words <= args.page_words):
        parser.error("invalid job count, timeout, anchor range, or fragment limits")
    required = ("X",) if args.code == "9053" else ("X", "Z")
    sectors = required if args.sector is None else (args.sector,)
    complete = anchors == set(range(12 * q)) and sectors == required
    destination = ROOT / f"Code{args.code}"
    prefix = f"{BASE}.Code{args.code}"
    logs = args.work / "build-logs"
    destination.mkdir(parents=True, exist_ok=True)
    logs.mkdir(parents=True, exist_ok=True)

    tables = []
    for side in ("X", "Z"):
        source = table_source(args.code, side, args.work / f"{p}-{side}.rows")
        update(destination / f"Words{side}.lean", source)
        tables.append(f"{prefix}.Words{side}")

    bases, pages, roots = [], [], []
    for side in sectors:
        generated = set()
        for offset, words in enumerate(read_binary(args.work / f"{p}-{side}.bin"), args.begin):
            if offset in anchors:
                base, *subpages, root = render_anchor(args.code, side, offset, words,
                    args.fragment_words, args.page_words, not args.separate_pages)
                bases.append(base)
                pages.extend(subpages)
                roots.append(root)
                generated.add(offset)
            if generated == anchors:
                break
        if generated != anchors:
            parser.error(f"missing {side} anchor programs {sorted(anchors - generated)}")
    if complete:
        update(destination / "Exact.lean", assemble_source(args.code, sectors, q))
    if args.generate_only:
        return
    if not build(f"{prefix}.Tables", args.timeout, logs, tables):
        raise SystemExit("the routed row tables did not pass kernel checks")
    for group in (bases, pages, roots, [f"{prefix}.Exact"] if complete else []):
        if not stage(group, args.jobs, args.timeout, logs):
            raise SystemExit("required kernel checks failed (see build logs)")


if __name__ == "__main__":
    main()
