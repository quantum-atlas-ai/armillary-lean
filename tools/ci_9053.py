"""Distribute 9053 kernel certificates and assemble the exact proof in one CI run."""

import argparse
import json
from pathlib import Path
import re
import subprocess

from build_reduced import stage
from render_reduced import BASE


WORK = Path(".lake/reduced")
CACHE = Path(".lake/9053-shards")
PLAN = WORK / "ci9053-plan.json"
MODULE = f"{BASE}.Code9053"
LOGS = WORK / "build-logs"
TABLES = [f"{MODULE}.WordsX", f"{MODULE}.WordsZ"]
CHUNKS = re.compile(rb"\.chunk (\d+) ")


def run(*args):
    subprocess.run(args, check=True)


def lake_targets(modules, *options):
    return [*(f"+{name}" for name in modules), *options]


def generate(anchors):
    args = ["python3", "-B", "tools/build_reduced.py", "9053", "--generate-only"]
    if anchors != list(range(36)):
        args += ["--anchors", *map(str, anchors)]
    run(*args)


def make_plan(smoke):
    anchors = [18, 35] if smoke else list(range(36))
    generate(anchors)
    roots = [f"{MODULE}.X{anchor:02d}" for anchor in anchors]
    pending = []
    for root in roots:
        path = Path(*root.split(".")).with_suffix(".lean")
        pages = [
            line.split()[-1]
            for line in path.read_text().splitlines()
            if line.startswith(f"public import {root}.Page")
        ]
        for module in pages or [root]:
            source = Path(*module.split(".")).with_suffix(".lean").read_bytes()
            weight = 600 + sum(map(int, CHUNKS.findall(source)))
            pending.append((weight, module))
    shards = [[] for _ in range(2 if smoke else 12)]
    weights = [0] * len(shards)
    for weight, module in sorted(pending, reverse=True):
        shard = min(range(len(shards)), key=weights.__getitem__)
        shards[shard].append(module)
        weights[shard] += weight
    if not all(shards):
        raise RuntimeError("each proof shard must have at least one target")
    PLAN.write_text(json.dumps({"anchors": anchors, "shards": shards, "roots": roots}) + "\n")
    print(f"Planned {len(pending)} Lean targets in {len(shards)} shards.", flush=True)


def verify_shard(plan, shard):
    targets = plan["shards"][shard]
    anchors = sorted({int(name.removeprefix(MODULE + ".X").split(".")[0]) for name in targets})
    generate(anchors)
    bases = [f"{MODULE}.X{anchor:02d}.Base" for anchor in anchors]
    run("lake", "build", *lake_targets([*TABLES, *bases]))
    if not stage(targets, 2, 1500, LOGS):
        for name in targets:
            log = LOGS / (name + ".log")
            if log.exists():
                lines = log.read_text(errors="replace").splitlines()
                if not any("Build completed successfully" in line or "All targets up-to-date" in line
                    for line in lines):
                    print("\n".join(lines[-35:]), flush=True)
        raise SystemExit("one or more proof shards failed kernel verification")
    mapping = WORK / f"ci9053-{shard}.jsonl"
    run("lake", "--no-build", "build", *lake_targets(targets, "-o", str(mapping)))
    run("lake", "cache", "stage", str(mapping), str(CACHE / f"shard-{shard}"))


def assemble(plan):
    generate(plan["anchors"])
    for shard in range(len(plan["shards"])):
        run("lake", "cache", "unstage", str(CACHE / f"shard-{shard}"))
    targets = [name for shard in plan["shards"] for name in shard]
    for start in range(0, len(targets), 64):
        run("lake", "--no-build", "build", *lake_targets(targets[start:start + 64]))
    final = [f"{MODULE}.Exact"] if len(plan["anchors"]) == 36 else plan["roots"]
    run("lake", "build", *lake_targets(final))
    run("python3", "tools/audit_axioms.py", *final)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=("plan", "verify", "assemble"))
    parser.add_argument("--smoke", action="store_true")
    parser.add_argument("--shard", type=int)
    args = parser.parse_args()
    if args.phase == "plan":
        make_plan(args.smoke)
        return
    plan = json.loads(PLAN.read_text())
    if args.phase == "verify":
        if args.shard is None or not 0 <= args.shard < len(plan["shards"]):
            parser.error("select a shard present in the plan")
        verify_shard(plan, args.shard)
    else:
        assemble(plan)


if __name__ == "__main__":
    main()
