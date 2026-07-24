#!/usr/bin/env python3
"""Register an external theorem and its verified application mapping."""

from __future__ import annotations

import argparse
from pathlib import Path

from _common import (
    append_event,
    append_jsonl,
    ensure_case,
    next_id,
    relative_to_case,
    resolve_case_path,
    utc_now,
)


STATUSES = ["proposed", "verified", "rejected"]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", type=Path, required=True)
    parser.add_argument("--theorem-id")
    statement = parser.add_mutually_exclusive_group(required=True)
    statement.add_argument("--statement")
    statement.add_argument("--statement-file", type=Path)
    parser.add_argument("--source-uri", required=True)
    parser.add_argument("--hypothesis", action="append", default=[])
    parser.add_argument("--application", action="append", default=[])
    parser.add_argument("--evidence-path")
    parser.add_argument("--status", choices=STATUSES, default="proposed")
    parser.add_argument("--actor", default="root")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    case = ensure_case(args.case)
    ledger = case / "state" / "external_theorems.jsonl"
    theorem_id = args.theorem_id or next_id(ledger, "theorem_id", "EXT")

    statement = args.statement
    if args.statement_file:
        statement = args.statement_file.read_text(encoding="utf-8").strip()
    assert statement is not None
    if not statement.strip():
        raise SystemExit("External theorem statement must be non-empty")
    if not args.source_uri.strip():
        raise SystemExit("External theorem source URI must be non-empty")

    evidence_path = None
    if args.evidence_path:
        resolved = resolve_case_path(
            case,
            args.evidence_path,
            must_exist=True,
            nonempty=True,
        )
        evidence_path = relative_to_case(case, resolved)

    if args.status == "verified":
        if not evidence_path:
            raise SystemExit("A verified external theorem requires --evidence-path")
        if not args.application:
            raise SystemExit(
                "A verified external theorem requires at least one --application"
            )

    now = utc_now()
    record = {
        "theorem_id": theorem_id,
        "statement": statement,
        "source_uri": args.source_uri,
        "hypotheses": args.hypothesis,
        "application_mapping": args.application,
        "evidence_path": evidence_path,
        "status": args.status,
        "created_at": now,
        "updated_at": now,
    }
    append_jsonl(ledger, record)
    append_event(
        case,
        actor=args.actor,
        action="external_theorem_recorded",
        affected_ids=[theorem_id],
        evidence_paths=[evidence_path] if evidence_path else [],
        details={"status": args.status, "source_uri": args.source_uri},
    )
    print(theorem_id)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
