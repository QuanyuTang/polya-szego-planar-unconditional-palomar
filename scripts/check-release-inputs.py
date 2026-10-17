#!/usr/bin/env python3
"""Check the reviewed production snapshot and frozen checksum coverage.

This packaging preflight runs no Lean/Lake and does not certify mathematics.
"""
from pathlib import Path, PurePosixPath
import hashlib
import json
import os
import re
import sys
import tomllib

ROOT = Path(__file__).resolve().parents[1]
TOOLCHAIN = "leanprover/lean4:v4.35.0-rc3"
MATHLIB = "c55e6e786f49471c72fbddbec5415808896aec1e"
ELLIPTIC = "ec784093f30308ef770ff855ce624725adf6f870"
RESULTS = ["BucklingChallenge." + name for name in (
    "area_inequality", "area_equality_iff", "polya_szego_buckling",
    "bucklingEig_ball", "buckling_ge_dirichlet")]
CRITICAL = [".gitattributes", ".gitignore", "lean-toolchain", "lakefile.toml", "lake-manifest.json", "LICENSE",
    "README.md", "comparator.json", "formalization.yaml", "requirements-ci.txt",
    "Gemfile", "Gemfile.lock", "verification/build-targets.txt",
    ".github/workflows/lean.yml", ".github/workflows/palomar.yml"]


def main() -> int:
    errors = []
    for obsolete in ("Challenge.lean", "Solution.lean"):
        if (ROOT / obsolete).exists():
            errors.append("obsolete generic submission wrapper/file is forbidden: " + obsolete)
    required = set(CRITICAL + ["PlanarBucklingChallenge.lean", "PlanarBucklingSolution.lean",
        "UnconditionalAreaFinalAudit.lean", "SubmissionSolutionAudit.lean",
        "verification/SHA256SUMS"])
    try:
        lake = tomllib.loads((ROOT / "lakefile.toml").read_text(encoding="utf-8"))
        submission_roots = ("PlanarBucklingChallenge", "PlanarBucklingSolution")
        library_roots = {lib["name"]: lib.get("roots", []) for lib in lake["lean_lib"]}
        if any(library_roots.get(name) != [name] for name in submission_roots) or any(name in library_roots for name in ("Challenge", "Solution")):
            errors.append("submission lean_lib names/roots must be the two unique modules")
        if not set(submission_roots).issubset(lake.get("defaultTargets", [])):
            errors.append("both unique submission libraries must be default targets")
        for lib in lake["lean_lib"]:
            required.update(name.replace(".", "/") + ".lean" for name in lib.get("roots", []))
    except (OSError, ValueError, KeyError) as error:
        errors.append(f"cannot read complete Lake roots: {error}")
    try:
        targets = (ROOT / "verification" / "build-targets.txt").read_text(encoding="utf-8").splitlines()
        for target in targets:
            if target.startswith("@/+"):
                module = target.removeprefix("@/+")
                if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.]*", module):
                    errors.append(f"invalid own-module build target: {target}")
                else:
                    required.add(module.replace(".", "/") + ".lean")
            elif not target.startswith("@EllipticPdes/+"):
                errors.append(f"unexpected build target: {target}")
        if not targets or targets[-4:] != ["@/+UnconditionalAreaFinalAudit", "@/+PlanarBucklingChallenge", "@/+PlanarBucklingSolution", "@/+SubmissionSolutionAudit"]:
            errors.append("build order must conclude with the final proof audit, unique challenge and solution roots, and the submission audit")
    except (OSError, UnicodeError) as error:
        errors.append(f"cannot read the reviewed build order: {error}")
    for relative in sorted(required):
        path = ROOT / relative
        if not path.is_file() or path.is_symlink():
            errors.append(f"missing regular production input: {relative}")
    if (ROOT / "lakefile.lean").exists():
        errors.append("exactly one Lakefile is required; lakefile.lean also exists")
    try:
        if (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip() != TOOLCHAIN:
            errors.append("toolchain differs from the reviewed rc3 pin")
        manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
        packages = {p["name"]: p for p in manifest["packages"]}
        for name, revision in [("mathlib", MATHLIB), ("EllipticPdes", ELLIPTIC)]:
            if packages[name]["rev"] != revision:
                errors.append(f"wrong actual dependency commit: {name}")
        if packages["EllipticPdes"].get("subDir") != "lean":
            errors.append("EllipticPdes must resolve its actual lean subdirectory")
        for package in manifest["packages"]:
            if package.get("type") != "git" or not re.fullmatch(r"[0-9a-f]{40}", package.get("rev", "")):
                errors.append(f"dependency lacks a full Git commit: {package.get('name')}")
            if not re.fullmatch(r"https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+(?:\.git)?", package.get("url", "")):
                errors.append(f"dependency URL is not public credential-free GitHub HTTPS: {package.get('name')}")
        config = json.loads((ROOT / "comparator.json").read_text(encoding="utf-8"))
        if config.get("challenge_module") != "PlanarBucklingChallenge" or config.get("solution_module") != "PlanarBucklingSolution":
            errors.append("unexpected Challenge/Solution module pair")
        if config.get("theorem_names") != RESULTS:
            errors.append("Comparator must retain all five reviewed original target names")
        if set(config.get("permitted_axioms", [])) != {"propext", "Quot.sound", "Classical.choice"}:
            errors.append("unexpected Comparator permitted axioms")
        if "external_kernels" in config:
            errors.append("submitted comparator.json must not contain external_kernels")
    except (OSError, ValueError, KeyError, TypeError) as error:
        errors.append(f"invalid fixed dependency/comparator input: {error}")
    challenge = ROOT / "PlanarBucklingChallenge.lean"
    if challenge.is_file():
        content = challenge.read_bytes()
        if len(content) > 100 * 1024 or len(content.splitlines()) > 1000:
            errors.append("Challenge exceeds the 100 KiB / 1000 physical-line hard limit")
    checked = {}
    checksum = ROOT / "verification" / "SHA256SUMS"
    if checksum.is_file():
        for number, line in enumerate(checksum.read_text(encoding="utf-8").splitlines(), 1):
            if not line.strip():
                continue
            match = re.fullmatch(r"([0-9a-f]{64}) [ *](.+)", line)
            if not match:
                errors.append(f"invalid checksum line {number}")
                continue
            digest, relative = match.groups()
            path = PurePosixPath(relative)
            if path.is_absolute() or ".." in path.parts or "\\" in relative or relative in checked:
                errors.append(f"unsafe or duplicate checksum path at line {number}")
                continue
            checked[relative] = digest
            actual = ROOT / relative
            if not actual.is_file() or actual.is_symlink():
                errors.append(f"checksum input is missing or is a symlink: {relative}")
            elif hashlib.sha256(actual.read_bytes()).hexdigest() != digest:
                errors.append(f"checksum mismatch: {relative}")
        must_hash = set(CRITICAL)
        for directory, subdirs, files in os.walk(ROOT, followlinks=False):
            subdirs[:] = [name for name in subdirs if name not in {".git", ".lake", "__pycache__"}]
            for name in files:
                path = Path(directory) / name
                if name.endswith(".lean") or path.parent == ROOT / "scripts" or ROOT / "vendor" in path.parents:
                    must_hash.add(path.relative_to(ROOT).as_posix())
        for relative in sorted(must_hash - checked.keys()):
            errors.append(f"frozen checksum coverage is missing: {relative}")
    if errors:
        for error in errors:
            print(f"error: {error}", file=sys.stderr)
        print("Production inputs are incomplete or inconsistent; verification stopped.", file=sys.stderr)
        return 1
    print("Production inputs and frozen checksum coverage are present; mathematics still needs native/kernel checks.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
