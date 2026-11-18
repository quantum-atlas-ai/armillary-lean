"""Generate, build and assemble the canonical 8749 kernel certificates."""

import argparse
import os
import subprocess
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

from render_min8749 import module_source, proof_source


MODULE = "ArmillaryLean.Instances.MinProof8749"
SOURCE = Path(*MODULE.split("."))
LOGS = Path(".lake/fast8749/build-logs")


def write_if_changed(path, source):
    if not path.exists() or path.read_text() != source:
        path.write_text(source)


def emit_family(programs, fragment_limit, page_limit):
    with programs.open() as source:
        rows = [list(map(int, line.split())) for line in source]
    if len(rows) != 36 or any(not row or any(not 0 <= w < 4096 for w in row) for row in rows):
        raise ValueError("expected 36 bounded word streams for the X-check matrix")
    groups = [(f"HeadX{i:02d}", range(i, i + 1)) for i in range(16)]
    groups.extend((("LateX", range(16, 20)), ("TailX", range(20, 33))))
    independent, assembled = [], []
    for name, indices in groups:
        pages = {}
        proof = [proof_source(rows[i], "X", 10, i, fragment_limit, pages if i < 9 else None,
            page_limit) for i in indices]
        page_names = []
        for start, body in pages.items():
            title = f"{name}Page{start}"
            write_if_changed(SOURCE / (title + ".lean"), module_source([body], "X"))
            page_names.append(title)
        imports = [f"{MODULE}.{title}" for title in page_names]
        write_if_changed(SOURCE / (name + ".lean"), module_source(proof, "X", imports))
        independent.extend(page_names)
        (assembled if page_names else independent).append(name)
    return [name for name, _ in groups], independent, assembled


def exact_source(modules):
    imports = "\n".join(f"public import {MODULE}.{name}" for name in modules)
    cases = [f"  · exact MinX{i:02d}.verified s ha hm hz hw" for i in range(33)]
    cases.extend("  · exact last_block_anchor 0 _ s ha hm hz" for _ in range(3))
    return f'''module

public import ArmillaryLean.Instances.Exact8749
{imports}
import Mathlib.Tactic.FinCases

@[expose] public section

namespace ArmillaryLean.Code8749

open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode (cssDistance)

set_option maxRecDepth 8192 in
/-- All minimum-rank obligations for the X-check matrix. -/
theorem minX : MinAnchorExclusions 0 := by
  intro b j s ha hm hz hw
  fin_cases b <;> fin_cases j
{chr(10).join(cases)}

/-- The actual Table S2 code has exact CSS distance twelve. -/
theorem distance_eq_twelve : cssDistance code = 12 := exact_of_min_x minX

#print axioms distance_eq_twelve

end ArmillaryLean.Code8749
'''


def build(name, limit):
    log = LOGS / (name + ".log")
    with log.open("w") as output:
        result = subprocess.run(
            ["timeout", str(limit), "lake", "build", f"+{MODULE}.{name}"],
            stdout=output,
            stderr=subprocess.STDOUT,
            env={**os.environ, "LAKE_ARTIFACT_CACHE": "true"},
            check=False,
        )
    print(f"{name} {result.returncode} {log}", flush=True)
    return result.returncode == 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("x", type=Path)
    parser.add_argument("--jobs", type=int, default=3)
    parser.add_argument("--timeout", type=int, default=1800)
    parser.add_argument("--fragment-words", type=int, default=500)
    parser.add_argument("--page-words", type=int, default=20000)
    parser.add_argument("--generate-only", action="store_true")
    args = parser.parse_args()
    if args.jobs < 1 or args.timeout < 1 or not 2 <= args.fragment_words <= args.page_words:
        parser.error("expected positive time and job limits and at least two words per fragment")
    SOURCE.mkdir(parents=True, exist_ok=True)
    LOGS.mkdir(parents=True, exist_ok=True)
    modules, independent, assembled = emit_family(args.x, args.fragment_words, args.page_words)
    write_if_changed(SOURCE / "Exact.lean", exact_source(modules))
    if args.generate_only:
        return
    independent.sort(key=lambda name: (SOURCE / (name + ".lean")).stat().st_size)
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        results = [pool.submit(build, name, args.timeout) for name in independent]
        passed = [result.result() for result in as_completed(results)]
        if all(passed):
            results = [pool.submit(build, name, args.timeout) for name in assembled]
            passed = [result.result() for result in as_completed(results)]
    if not all(passed) or not build("Exact", args.timeout):
        raise SystemExit("the required kernel proofs have not all passed")


if __name__ == "__main__":
    main()
