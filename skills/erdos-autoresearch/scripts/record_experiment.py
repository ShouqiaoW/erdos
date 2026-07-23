#!/usr/bin/env python3
"""Execute or record a reproducible experiment with provenance."""

from __future__ import annotations

import argparse
import os
import platform
import shlex
import subprocess
import sys
from pathlib import Path

from _common import (
    append_event,
    ensure_case,
    next_id,
    relative_to_case,
    resolve_case_path,
    sha256_file,
    split_csv,
    utc_now,
    write_json,
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", type=Path, required=True)
    parser.add_argument("--description", required=True)
    parser.add_argument("--command", required=True)
    parser.add_argument(
        "--interpretation",
        required=True,
        help="State exactly what the result does and does not establish.",
    )
    parser.add_argument("--cwd", type=Path)
    parser.add_argument("--claims")
    parser.add_argument("--source-files")
    parser.add_argument("--seed")
    parser.add_argument("--timeout-seconds", type=int, default=3600)
    parser.add_argument("--record-only", action="store_true")
    parser.add_argument("--release-relevant", action="store_true")
    parser.add_argument("--independently-reproduced", action="store_true")
    parser.add_argument("--actor", default="computationalist")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    case = ensure_case(args.case)
    registry = case / "state" / "experiments.jsonl"
    experiment_id = next_id(registry, "experiment_id", "EXP")
    experiment_dir = case / "experiments" / experiment_id
    experiment_dir.mkdir(parents=True, exist_ok=False)
    cwd = (args.cwd or case).resolve()
    source_files = [
        resolve_case_path(case, item, must_exist=True, nonempty=True)
        for item in split_csv(args.source_files)
    ]
    source_hashes = {
        relative_to_case(case, path): sha256_file(path) for path in source_files
    }

    started_at = utc_now()
    return_code = None
    timed_out = False
    stdout_path = experiment_dir / "stdout.txt"
    stderr_path = experiment_dir / "stderr.txt"

    if args.record_only:
        stdout_path.write_text("", encoding="utf-8")
        stderr_path.write_text("", encoding="utf-8")
    else:
        command = shlex.split(args.command)
        try:
            result = subprocess.run(
                command,
                cwd=cwd,
                text=True,
                capture_output=True,
                timeout=args.timeout_seconds,
                check=False,
                env={**os.environ, **({"RESEARCH_SEED": args.seed} if args.seed else {})},
            )
            return_code = result.returncode
            stdout_path.write_text(result.stdout, encoding="utf-8")
            stderr_path.write_text(result.stderr, encoding="utf-8")
        except subprocess.TimeoutExpired as exc:
            timed_out = True
            stdout_path.write_text(exc.stdout or "", encoding="utf-8")
            stderr_path.write_text(exc.stderr or "", encoding="utf-8")

    ended_at = utc_now()
    record = {
        "experiment_id": experiment_id,
        "description": args.description,
        "command": args.command,
        "cwd": str(cwd),
        "claims": split_csv(args.claims),
        "seed": args.seed,
        "started_at": started_at,
        "ended_at": ended_at,
        "timeout_seconds": args.timeout_seconds,
        "timed_out": timed_out,
        "return_code": return_code,
        "record_only": args.record_only,
        "release_relevant": args.release_relevant,
        "source_hashes": source_hashes,
        "stdout_sha256": sha256_file(stdout_path),
        "stderr_sha256": sha256_file(stderr_path),
        "environment": {
            "python": sys.version,
            "platform": platform.platform(),
        },
        "interpretation": args.interpretation,
        "reproduced_by_independent_checker": args.independently_reproduced,
    }
    write_json(experiment_dir / "manifest.json", record)

    from _common import append_jsonl
    append_jsonl(registry, record)
    append_event(
        case,
        actor=args.actor,
        action="experiment_recorded",
        affected_ids=[experiment_id, *record["claims"]],
        evidence_paths=[
            f"experiments/{experiment_id}/manifest.json",
            f"experiments/{experiment_id}/stdout.txt",
            f"experiments/{experiment_id}/stderr.txt",
        ],
        details={"return_code": return_code, "timed_out": timed_out},
    )
    print(experiment_id)
    return 0 if not timed_out and (return_code in {None, 0}) else 1


if __name__ == "__main__":
    raise SystemExit(main())
