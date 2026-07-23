#!/usr/bin/env python3
"""Freeze the authoritative problem statement and record provenance."""

from __future__ import annotations

import argparse
import shutil
from pathlib import Path

from _common import append_event, ensure_case, load_json, sha256_file, utc_now, write_json


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", type=Path, required=True)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--source-uri", default="")
    parser.add_argument("--published-or-updated-at")
    parser.add_argument("--force", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    case = ensure_case(args.case)
    source = args.input.resolve()
    if not source.exists() or not source.is_file():
        raise SystemExit(f"Input file not found: {source}")

    target = case / "source" / "original_statement.md"
    if target.exists() and not args.force:
        old_hash = sha256_file(target)
        new_hash = sha256_file(source)
        if old_hash != new_hash:
            raise SystemExit(
                "A different statement is already frozen. Use --force only after "
                "creating a contract rollback obligation."
            )

    shutil.copyfile(source, target)
    digest = sha256_file(target)
    provenance = {
        "source_uri": args.source_uri,
        "retrieved_at": utc_now(),
        "published_or_updated_at": args.published_or_updated_at,
        "sha256": digest,
        "frozen_path": "source/original_statement.md",
    }
    write_json(case / "source" / "provenance.json", provenance)

    contract_path = case / "contract" / "problem_contract.json"
    contract = load_json(contract_path)
    contract["source"] = {
        "uri": args.source_uri,
        "sha256": digest,
        "retrieved_at": provenance["retrieved_at"],
        "published_or_updated_at": args.published_or_updated_at,
    }
    write_json(contract_path, contract)

    checkpoint = load_json(case / "state" / "checkpoint.json")
    checkpoint["phase"] = "STATEMENT_FROZEN"
    checkpoint["next_actions"] = [
        "Compile exact proof contract",
        "Run two independent semantic audits",
    ]
    write_json(case / "state" / "checkpoint.json", checkpoint)

    append_event(
        case,
        actor="freeze_statement.py",
        action="statement_frozen",
        evidence_paths=["source/original_statement.md", "source/provenance.json"],
        details={"sha256": digest, "source_uri": args.source_uri},
    )
    print(digest)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
