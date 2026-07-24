#!/usr/bin/env python3
"""Package a case release only after a passing gate report exists."""

from __future__ import annotations

import argparse
import os
import subprocess
import sys
import tempfile
import zipfile
from pathlib import Path

from _common import (
    ResearchStateError,
    ensure_case,
    load_json,
    resolve_case_path,
    sha256_file,
    write_json,
)


INCLUDE_DIRS = [
    "source",
    "contract",
    "state",
    "routes",
    "claims",
    "proof",
    "audit",
    "formal",
    "release",
    "experiments",
]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    return parser.parse_args()


def is_previous_package(path: Path, case: Path) -> bool:
    try:
        relative = path.relative_to(case)
    except ValueError:
        return False
    if not relative.parts or relative.parts[0] != "release":
        return False
    return path.suffix == ".zip" or path.name.endswith(".zip.manifest.json")


def collect_release_files(case: Path, output: Path) -> list[Path]:
    files: list[Path] = []
    seen: set[Path] = set()

    def add(path: Path) -> None:
        resolved = path.resolve()
        if resolved not in seen:
            files.append(resolved)
            seen.add(resolved)

    for filename in ["run_config.json", "STATUS.md"]:
        path = case / filename
        if path.is_symlink():
            raise SystemExit(f"Refusing symlinked release artifact: {path}")
        if path.exists() and path.is_file():
            add(path)

    for directory in INCLUDE_DIRS:
        base = case / directory
        if not base.exists():
            continue
        if base.is_symlink():
            raise SystemExit(f"Refusing symlinked release directory: {base}")
        for path in sorted(base.rglob("*")):
            if path.is_symlink():
                raise SystemExit(f"Refusing symlinked release artifact: {path}")
            if not path.is_file():
                continue
            if path.resolve() == output or is_previous_package(path, case):
                continue
            add(path)

    freeze = load_json(case / "audit" / "candidate_freeze.json")
    frozen_artifacts = freeze.get("artifacts")
    if not isinstance(frozen_artifacts, dict):
        raise SystemExit("Candidate freeze artifacts must be an object")
    for artifact in frozen_artifacts.values():
        if not isinstance(artifact, dict):
            raise SystemExit("Malformed candidate freeze artifact")
        try:
            path = resolve_case_path(
                case,
                str(artifact.get("path", "")),
                must_exist=True,
            )
        except ResearchStateError as exc:
            raise SystemExit(f"Invalid frozen artifact: {exc}") from exc
        if path.is_symlink():
            raise SystemExit(f"Refusing symlinked release artifact: {path}")
        add(path)
    return files


def main() -> int:
    args = parse_args()
    case = ensure_case(args.case)
    gate_path = case / "release" / "gate_report.json"
    gate = load_json(gate_path)
    if not gate.get("passed"):
        raise SystemExit("Release gate has not passed")
    if gate.get("status") != "INTERNALLY_AUDITED_CANDIDATE":
        raise SystemExit("Release gate has an invalid automated status")
    final_claim = gate.get("final_claim")
    if not isinstance(final_claim, str) or not final_claim:
        raise SystemExit("Release gate report has no final claim")

    gate_script = Path(__file__).with_name("release_gate.py")
    revalidation = subprocess.run(
        [
            sys.executable,
            str(gate_script),
            "--case",
            str(case),
            "--status",
            "INTERNALLY_AUDITED_CANDIDATE",
            "--final-claim",
            final_claim,
        ],
        text=True,
        capture_output=True,
        check=False,
    )
    if revalidation.returncode != 0:
        details = "\n".join(
            part.strip()
            for part in [revalidation.stdout, revalidation.stderr]
            if part.strip()
        )
        raise SystemExit(f"Release gate revalidation failed:\n{details}")

    output = args.output or case / "release" / f"{case.name}-candidate-package.zip"
    output = output.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)

    files = collect_release_files(case, output)
    before = {path: sha256_file(path) for path in files}
    manifest = {
        f"{case.name}/{path.relative_to(case)}": digest
        for path, digest in before.items()
    }

    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{output.name}.",
        suffix=".tmp",
        dir=output.parent,
    )
    os.close(descriptor)
    temporary = Path(temporary_name)
    try:
        with zipfile.ZipFile(
            temporary,
            "w",
            compression=zipfile.ZIP_DEFLATED,
        ) as archive:
            for path in files:
                arcname = f"{case.name}/{path.relative_to(case)}"
                archive.write(path, arcname)
        with zipfile.ZipFile(temporary) as archive:
            corrupt = archive.testzip()
            if corrupt:
                raise SystemExit(f"Generated archive is corrupt at: {corrupt}")

        after = {path: sha256_file(path) for path in files}
        changed = [
            str(path.relative_to(case))
            for path in files
            if before[path] != after[path]
        ]
        if changed:
            raise SystemExit(
                "Case artifacts changed during packaging:\n- "
                + "\n- ".join(changed)
            )
        os.replace(temporary, output)
    finally:
        if temporary.exists():
            temporary.unlink()

    write_json(
        output.with_suffix(output.suffix + ".manifest.json"),
        {
            "archive": str(output),
            "archive_sha256": sha256_file(output),
            "files": manifest,
        },
    )
    print(output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
