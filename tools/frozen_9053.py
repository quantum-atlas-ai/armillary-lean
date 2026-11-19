"""Package or audit the checked 9053 proof without rebuilding its certificate pages."""

import argparse
from hashlib import file_digest
import json
from pathlib import Path
from platform import machine, system
import re
from shutil import copy2
import subprocess
import tarfile
from tempfile import TemporaryDirectory

from ci_9053 import MODULE, WORK, run


EXACT = f"{MODULE}.Exact"
THEOREM = "ArmillaryLean.Code9053.distance_eq_fourteen"
INPUTS = ("137-X.rows", "137-Z.rows", "137-X.bin")
DEPENDENCIES = ("lean-toolchain", "lakefile.toml", "lake-manifest.json")
PROOF_SOURCES = (*DEPENDENCIES, "ArmillaryLean.lean", "ArmillaryLean",
                 "tools/build_reduced.py", "tools/render_reduced.py", "tools/render8749.py")
HERE = Path(__file__).resolve().parent
LOCK = HERE.parent / "artifacts" / "9053.json"


def sha256(path):
    with Path(path).open("rb") as stream:
        return file_digest(stream, "sha256").hexdigest()


def proof_environment():
    return {
        "system": system(),
        "arch": machine(),
        "toolchain": Path("lean-toolchain").read_text().strip(),
        "dependencies": {name: sha256(name) for name in DEPENDENCIES},
    }


def assert_source_revision(revision):
    if not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise ValueError("expected a full commit SHA for the proof source")
    run("git", "diff", "--exit-code", revision, "--", *PROOF_SOURCES)


def regenerate(inputs):
    run("python3", "-B", "tools/build_reduced.py", "9053",
        "--work", str(inputs), "--generate-only")


def verify_exact(work, mapping=None):
    command = ["lake", "--no-build", "build", f"+{EXACT}"]
    if mapping is not None:
        command += ["-o", str(mapping)]
    run(*command)
    probe = work / "CheckFrozen9053.lean"
    probe.write_text(f"""module

import {EXACT}

open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode (cssDistance)

example : cssDistance ArmillaryLean.Code9053.code = 14 := {THEOREM}

#print axioms {THEOREM}
""")
    run("lake", "--no-build", "lean", str(probe))
    run("python3", "-B", "tools/audit_axioms.py", EXACT)


def pack(archive, inputs, revision, verified_run):
    assert_source_revision(revision)
    archive = archive.resolve()
    if archive.exists():
        raise ValueError(f"archive already exists: {archive}")
    archive.parent.mkdir(parents=True, exist_ok=True)
    regenerate(inputs)
    with TemporaryDirectory(dir=archive.parent, prefix="staging-") as temporary:
        staging = Path(temporary)
        payload = staging / "payload"
        (payload / "inputs").mkdir(parents=True)
        for name in INPUTS:
            copy2(inputs / name, payload / "inputs" / name)
        mapping = staging / "targets.jsonl"
        verify_exact(staging, mapping)
        run("lake", "cache", "stage", str(mapping), str(payload / "lake-cache"))
        manifest = {
            "format": 1,
            "proof_commit": revision,
            "verified_run": verified_run,
            "module": EXACT,
            "theorem": THEOREM,
            "environment": proof_environment(),
            "inputs": {name: sha256(payload / "inputs" / name) for name in INPUTS},
        }
        (payload / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
        packed = staging / "archive.tar.zst"
        run("tar", "--sort=name", "--mtime=@0", "--owner=0", "--group=0", "--numeric-owner",
            "--hard-dereference", "-I", "zstd -3 -T2", "-C", str(payload),
            "-cf", str(packed), "manifest.json", "inputs", "lake-cache")
        packed.replace(archive)
    print(f"SHA-256 {sha256(archive)}  {archive}", flush=True)


def unpack(archive, destination):
    def safe_member(member, target):
        parts = Path(member.name).parts
        if (not parts or parts[0] not in {"manifest.json", "inputs", "lake-cache"}
                or ".." in parts or not (member.isfile() or member.isdir())):
            raise ValueError(f"unexpected archive member: {member.name}")
        return tarfile.data_filter(member, target)

    with subprocess.Popen(["zstd", "-dc", "--", str(archive)], stdout=subprocess.PIPE) as decoder:
        try:
            with tarfile.open(fileobj=decoder.stdout, mode="r|") as bundle:
                bundle.extractall(destination, filter=safe_member)
            decoder.stdout.read()
        except BaseException:
            decoder.terminate()
            raise
        if decoder.wait() != 0:
            raise ValueError("zstd decompression failed")


def audit(archive, lock, staging):
    expected = json.loads(lock.read_text())
    archive = archive.resolve()
    if sha256(archive) != expected["sha256"]:
        raise ValueError("archive SHA-256 does not match the proof lock")
    print(f"Verified archive SHA-256 {expected['sha256']}", flush=True)
    revision = expected["proof_commit"]
    if not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise ValueError("invalid proof commit in lock")
    run("git", "cat-file", "-e", f"{revision}^{{commit}}")
    with TemporaryDirectory(dir=staging, prefix="restore-") as temporary:
        root = Path(temporary)
        unpack(archive, root)
        manifest = json.loads((root / "manifest.json").read_text())
        if (manifest["format"] != 1 or manifest["module"] != EXACT or manifest["theorem"] != THEOREM
                or manifest["proof_commit"] != expected["proof_commit"]
                or manifest["verified_run"] != expected["verified_run"]
                or manifest["environment"] != proof_environment()):
            raise ValueError("proof manifest is incompatible with this checkout")
        inputs = root / "inputs"
        if {name: sha256(inputs / name) for name in INPUTS} != manifest["inputs"]:
            raise ValueError("certificate inputs do not match the manifest")
        regenerate(inputs)
        run("lake", "cache", "unstage", str(root / "lake-cache"))
        verify_exact(root)
    print(f"Audited frozen theorem {THEOREM} at {expected['proof_commit']}", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    pack_args = commands.add_parser("pack", help="freeze a complete, already compiled proof")
    pack_args.add_argument("archive", type=Path)
    pack_args.add_argument("--inputs", type=Path, default=WORK)
    pack_args.add_argument("--proof-commit")
    pack_args.add_argument("--verified-run", type=int)
    audit_args = commands.add_parser("audit", help="restore and audit a pinned proof archive")
    audit_args.add_argument("archive", type=Path)
    audit_args.add_argument("--lock", type=Path, default=LOCK)
    args = parser.parse_args()
    if args.command == "pack":
        revision = args.proof_commit or subprocess.check_output(
            ["git", "rev-parse", "HEAD"], text=True).strip()
        pack(args.archive, args.inputs, revision, args.verified_run)
    else:
        staging = Path(".lake/frozen-9053")
        staging.mkdir(parents=True, exist_ok=True)
        audit(args.archive, args.lock, staging)


if __name__ == "__main__":
    main()
