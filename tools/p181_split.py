"""Compile, package, audit and join locally checked p181 anchor proofs."""

import argparse
from concurrent.futures import ThreadPoolExecutor
from hashlib import file_digest, sha256
import json
import os
from pathlib import Path
from platform import machine, system
import re
from shutil import copy2, disk_usage
import subprocess
import tarfile
from tempfile import TemporaryDirectory

from audit_axioms import AUDIT
from build_reduced import assemble_source
from render_reduced import BASE

PREFIX = f"{BASE}.CodeP181"
EXACT = f"{PREFIX}.Exact"
DISTANCES = "ArmillaryLean.Instances.ReducedDistances"
TABLES = [f"{PREFIX}.Words{side}" for side in "XZ"]
WORK = Path(".lake/p181-split-proof")
BUILD = Path(".lake/build")
MANIFEST = "p181-manifest.json"
COMMON = "p181-common.tar.zst"
FULL = [f"{side}{n:02d}" for side in "XZ" for n in range(48)]
SMOKE = ["X28", "Z28"]
OLEAN_SUFFIXES = (".olean", ".olean.server", ".olean.private")
MAX_ASSET = 2**31


def run(*cmd, **kwargs):
    return subprocess.run(cmd, check=True, **kwargs)


def output(*cmd):
    return subprocess.check_output(cmd, text=True).strip()


def digest(path):
    with path.open("rb") as f:
        return file_digest(f, "sha256").hexdigest()


def write_json(path, obj):
    path.write_text(json.dumps(obj, sort_keys=True, indent=2) + "\n")


def module_path(name):
    return Path(*name.split("."))


def get_env(extra=()):
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(
        [str(p.resolve()) for p in extra] + [output("lake", "env", "printenv", "LEAN_PATH")])
    return env


def identity():
    return {
        "proof_commit": output("git", "rev-parse", "HEAD"),
        "toolchain": Path("lean-toolchain").read_text().strip(),
        "lake_manifest_sha256": digest(Path("lake-manifest.json")),
        "platform": f"{system()}/{machine()}",
    }


def anchors(scope):
    return SMOKE if scope == "smoke" else FULL


def split_plan(scope, work):
    weights = {}
    for side in "XZ":
        for line in (work / f"{side}-search.log").read_text().splitlines():
            index, _, _, words = map(int, line.split())
            weights[f"{side}{index:02d}"] = words
    groups = [[] for _ in range(2 if scope == "smoke" else 16)]
    loads = [0] * len(groups)
    for anchor in sorted(anchors(scope), key=weights.__getitem__, reverse=True):
        i = min(range(len(loads)), key=loads.__getitem__)
        groups[i].append(anchor)
        loads[i] += weights[anchor]
    return [sorted(group) for group in groups]


def modules_for(anchor):
    root = f"{PREFIX}.{anchor}"
    imports = module_path(root).with_suffix(".lean").read_text().splitlines()
    return [line.split()[-1] for line in imports if line.startswith(f"public import {root}.")] + [root]


def compile_modules(names, out, env, state, workers, timeout):
    lean = output("elan", "which", "lean")
    repo = Path.cwd()
    logs = out / "logs"
    logs.mkdir(parents=True, exist_ok=True)

    def compile_one(name):
        relative = module_path(name)
        src = relative.with_suffix(".lean")
        if not src.exists():
            raise ValueError(f"missing generated source {src}")
        dest = out / relative
        stamp = dest.with_suffix(".ready")
        source_stamp = sha256((state + digest(src)).encode()).hexdigest()
        if (stamp.exists() and stamp.read_text() == source_stamp
                and all(dest.with_suffix(suffix).is_file() for suffix in OLEAN_SUFFIXES)):
            return
        dest.parent.mkdir(parents=True, exist_ok=True)
        with TemporaryDirectory(dir=dest.parent, prefix="compile-") as tmp:
            obj = Path(tmp) / dest.name
            with (logs / f"{name}.log").open("w") as log:
                result = subprocess.run(
                    [lean, f"--root={repo}", "--threads=1", "-DautoImplicit=false",
                     "-DwarningAsError=true", str(src), "-o", str(obj.with_suffix(".olean"))],
                    env=env, stdout=log, stderr=subprocess.STDOUT, timeout=timeout)
            if result.returncode:
                raise RuntimeError(f"Lean failed for {name}. See {logs / (name + '.log')}")
            for suffix in OLEAN_SUFFIXES:
                obj.with_suffix(suffix).replace(dest.with_suffix(suffix))
        stamp.write_text(source_stamp)

    with ThreadPoolExecutor(max_workers=workers) as pool:
        for start in range(0, len(names), 64):
            batch = names[start:start + 64]
            list(pool.map(compile_one, batch))
            print(f"Local Lean checks {min(start+64, len(names))}/{len(names)}", flush=True)


def make_archive(out, asset, files_root, paths):
    destination = out / asset
    temp = destination.with_suffix(".part")
    listing = out / (asset + ".files")
    listing.write_text("\n".join(map(str, sorted(paths))) + "\n")
    run("tar", "--hard-dereference", "--sort=name", "--mtime=@0", "--owner=0", "--group=0",
        "--numeric-owner", "-I", "zstd -3 -T4", "-cf", str(temp), "-C", str(files_root),
        "-T", str(listing))
    listing.unlink()
    size = temp.stat().st_size
    if size >= MAX_ASSET:
        raise ValueError(f"{asset} exceeds the release asset size limit")
    temp.replace(destination)
    return {"archive": asset, "sha256": digest(destination), "bytes": size}


def proof_paths(names):
    return [module_path(name).with_suffix(ext) for name in names for ext in OLEAN_SUFFIXES]


def common_modules(out):
    names = set()
    pending = [*TABLES, DISTANCES]
    pattern = re.compile(r"^(?:public )?(?:meta )?import (?:all )?(ArmillaryLean\.[\w.]+)$", re.M)
    while pending:
        name = pending.pop()
        if name in names:
            continue
        names.add(name)
        pending.extend(pattern.findall(module_path(name).with_suffix(".lean").read_text()))
    for path in proof_paths(names):
        target = out / path
        target.parent.mkdir(parents=True, exist_ok=True)
        with TemporaryDirectory(dir=target.parent, prefix="shared-") as tmp:
            staged = Path(tmp) / target.name
            copy2(BUILD / "lib/lean" / path, staged)
            staged.replace(target)
    return sorted(names)


def local(args):
    work = args.work.resolve()
    if not (work / "sources-ready").exists():
        raise ValueError("wait for generation and independent replay of both certificate streams")
    if output("git", "status", "--porcelain", "--untracked-files=no"):
        raise ValueError("commit proof source changes before freezing artifacts")
    metadata = identity()
    out = work / "compiled"
    out.mkdir(parents=True, exist_ok=True)
    bundle = work / args.scope
    bundle.mkdir(parents=True, exist_ok=True)
    groups = split_plan(args.scope, work)
    sources = {anchor: modules_for(anchor) for group in groups for anchor in group}
    run("lake", "build", *(f"+{name}" for name in [DISTANCES, *TABLES]))
    common = common_modules(out)
    shared_hashes = {str(path): digest(out / path) for path in proof_paths(common)}
    stamp = json.dumps([metadata["toolchain"], metadata["lake_manifest_sha256"],
                        metadata["platform"], shared_hashes], sort_keys=True)
    stamp += digest(work / "inputs.sha256")
    env = get_env([out])
    bases = [mods[0] for mods in sources.values()]
    pages = [page for mods in sources.values() for page in mods[1:-1]]
    compile_modules(bases, out, env, stamp, min(args.workers, 8), 600)
    print(f"Compiling {len(pages)} certificate pages", flush=True)
    compile_modules(pages, out, env, stamp, args.workers, 1200)
    print(f"Assembling {len(sources)} anchors", flush=True)
    anchor_state = stamp + "".join(
        (out / module_path(name).with_suffix(".ready")).read_text()
        for name in [*bases, *pages])
    compile_modules([mods[-1] for mods in sources.values()], out, env, anchor_state, 3, 2400)
    manifest = {"format": 1, **metadata, "scope": args.scope, "parts": []}
    manifest["inputs_sha256"] = {p.name: digest(p) for p in sorted(work.glob("181-*.rows"))}
    manifest["inputs_sha256"].update({p.name: digest(p) for p in sorted(work.glob("181-*.bin"))})
    manifest["common"] = {**make_archive(bundle, COMMON, out, proof_paths(common)),
                          "modules": common}
    for i, group in enumerate(groups):
        names = [module for anchor in group for module in sources[anchor]]
        package = make_archive(bundle, f"p181-shard-{i:02d}.tar.zst", out, proof_paths(names))
        manifest["parts"].append({"id": i, "anchors": group, "modules": names, **package})
        print(f"Packed shard {i}, {len(names)} Lean modules", flush=True)
    write_json(bundle / MANIFEST, manifest)
    print(f"Manifest SHA-256 {digest(bundle / MANIFEST)}", flush=True)


def load_manifest(directory, expected):
    path = directory / MANIFEST
    if not re.fullmatch(r"[a-f0-9]{64}", expected) or digest(path) != expected:
        raise ValueError("manifest SHA-256 mismatch")
    manifest = json.loads(path.read_text())
    if (manifest["format"] != 1 or manifest["scope"] not in {"smoke", "full"}
            or any(manifest[key] != value for key, value in identity().items())):
        raise ValueError("manifest does not match the checkout, toolchain and platform")
    found = sorted(anchor for part in manifest["parts"] for anchor in part["anchors"])
    if found != sorted(anchors(manifest["scope"])):
        raise ValueError("anchor coverage mismatch")
    shard_count = 2 if manifest["scope"] == "smoke" else 16
    if [part["id"] for part in manifest["parts"]] != list(range(shard_count)):
        raise ValueError("invalid shard numbering")
    if manifest["common"]["archive"] != COMMON:
        raise ValueError("unexpected shared archive name")
    for module in manifest["common"]["modules"]:
        if not re.fullmatch(r"ArmillaryLean(?:\.[A-Za-z_][A-Za-z0-9_]*)+", module):
            raise ValueError("unexpected shared module")
        if module.startswith(PREFIX + ".") and module not in TABLES:
            raise ValueError("a proof module appears in the shared archive")
    for part in manifest["parts"]:
        if part["archive"] != f"p181-shard-{part['id']:02d}.tar.zst":
            raise ValueError("unexpected shard archive name")
        roots = {f"{PREFIX}.{anchor}" for anchor in part["anchors"]}
        if not roots.issubset(part["modules"]) or len(part["modules"]) != len(set(part["modules"])):
            raise ValueError("unexpected or missing anchor modules")
        for module in part["modules"]:
            root, _, suffix = module.rpartition(".")
            if module not in roots and (root not in roots or not re.fullmatch(r"Base|Page\d+", suffix)):
                raise ValueError(f"unexpected proof module {module}")
    return manifest


def unpack(directory, entry, into):
    archive = directory / entry["archive"]
    if digest(archive) != entry["sha256"] or archive.stat().st_size != entry["bytes"]:
        raise ValueError(f"archive digest or length mismatch: {archive.name}")
    into.mkdir(exist_ok=True)
    names = {str(p) for p in proof_paths(entry["modules"])}
    with subprocess.Popen(["zstd", "-dc", "--", str(archive)], stdout=subprocess.PIPE) as proc:
        seen = set()
        try:
            with tarfile.open(fileobj=proc.stdout, mode="r|") as tar:
                for member in tar:
                    if not member.isfile() or member.name not in names or member.name in seen:
                        raise ValueError(f"unexpected file in proof archive: {member.name}")
                    tar.extract(member, into, filter="data")
                    seen.add(member.name)
            proc.stdout.read()
        except BaseException:
            proc.terminate()
            raise
        if proc.wait() or seen != names:
            raise ValueError(f"incomplete proof archive: {archive.name}")


def audit(args, manifest):
    part = manifest["parts"][args.shard]
    imports = [*manifest["common"]["modules"], *part["modules"]]
    receipt_dir = args.out.resolve()
    receipt_dir.mkdir(parents=True, exist_ok=True)
    with TemporaryDirectory() as tmp:
        root = Path(tmp)
        proof = root / "proof"
        unpack(args.directory, manifest["common"], proof)
        unpack(args.directory, part, proof)
        unpacked = sum(p.stat().st_size for p in proof.rglob("*") if p.is_file())
        print(f"Auditing {len(imports)} modules with {unpacked:,} unpacked bytes. "
              f"Temporary disk has {disk_usage(root).free:,} free bytes.", flush=True)
        source = root / "P181ShardAudit.lean"
        source.write_text("module\n\nmeta import Lean\n" +
                          "".join(f"import all {name}\n" for name in imports) + AUDIT)
        run("lean", str(source), env=get_env([proof]))
        exported = {}
        for module in part["modules"]:
            relative = module_path(module).with_suffix(".olean")
            target = receipt_dir / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            copy2(proof / relative, target)
            exported[module] = digest(target)
        write_json(receipt_dir / "receipt.json",
                   {"manifest_sha256": args.sha256, "shard": args.shard, "exported": exported})


def join(args, manifest):
    received = {}
    all_receipts = {}
    for receipt in args.receipts.glob("*/receipt.json"):
        info = json.loads(receipt.read_text())
        index = info["shard"]
        if index in all_receipts or info["manifest_sha256"] != args.sha256:
            raise ValueError("unexpected or duplicate audit receipt")
        all_receipts[index] = (receipt.parent, info["exported"])
    for part in manifest["parts"]:
        folder, exported = all_receipts[part["id"]]
        if set(exported) != set(part["modules"]):
            raise ValueError("receipt module coverage mismatch")
        for module, sha in exported.items():
            path = folder / module_path(module).with_suffix(".olean")
            if module in received or digest(path) != sha:
                raise ValueError(f"unexpected or changed public artifact: {module}")
            received[module] = [[str(path.resolve())]]
    if set(all_receipts) != {part["id"] for part in manifest["parts"]}:
        raise ValueError("audit receipt coverage mismatch")
    with TemporaryDirectory() as tmp:
        root = Path(tmp)
        shared = root / "common"
        unpack(args.directory, manifest["common"], shared)
        if manifest["scope"] == "full":
            source = assemble_source("P181", ("X", "Z"), 4)
            name = EXACT
            theorem = "ArmillaryLean.CodeP181.distance_eq_sixteen"
        else:
            imports = "".join(f"public import {PREFIX}.{a}\n" for a in SMOKE)
            source = f"""module

{imports}
open ArmillaryLean.CodeP181

/-- Both pilot anchors assemble from the audited public modules. -/
public theorem auditedAnchors :
    (fun {{p : Prop}} (_ : p) => p) (And.intro X28.verified Z28.verified) :=
  And.intro X28.verified Z28.verified

#print axioms auditedAnchors
"""
            name = "P181AuditSmoke"
            theorem = "auditedAnchors"
        source = source.replace("module\n", "module\n\nmeta import Lean\n", 1)
        source += f"""
open Lean in
#eval show CoreM Unit from do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  for axiomName in ← collectAxioms `{theorem} do
    unless allowed.contains axiomName do
      throwError "Unexpected axiom {{axiomName}} in the final claim"
"""
        args.out.mkdir(parents=True, exist_ok=True)
        check = args.out / "Final.lean"
        check.write_text(source)
        setup = root / "setup.json"
        write_json(setup, {
            "name": name, "isModule": True, "importArts": received, "dynlibs": [],
            "plugins": [], "options": {"autoImplicit": False, "warningAsError": True},
        })
        run("lean", f"--setup={setup}", str(check), "-o", str(args.out / "Final.olean"),
            env=get_env([shared]))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    local_args = commands.add_parser("local")
    local_args.add_argument("scope", choices=("smoke", "full"))
    local_args.add_argument("--workers", type=int, default=16)
    local_args.add_argument("--work", type=Path, default=WORK)
    for command in ("plan", "audit", "join"):
        part = commands.add_parser(command)
        part.add_argument("directory", type=Path)
        part.add_argument("sha256")
        if command == "audit":
            part.add_argument("shard", type=int)
            part.add_argument("out", type=Path)
        if command == "join":
            part.add_argument("receipts", type=Path)
            part.add_argument("out", type=Path)
    args = parser.parse_args()
    if args.command == "local":
        local(args)
        return
    manifest = load_manifest(args.directory, args.sha256)
    if args.command == "plan":
        print(json.dumps([part["id"] for part in manifest["parts"]]))
    elif args.command == "audit":
        audit(args, manifest)
    else:
        join(args, manifest)


if __name__ == "__main__":
    main()
