#!/usr/bin/env python3
"""Append a proof, audit, contract, computation, or formalization obligation."""

from __future__ import annotations

import argparse
from pathlib import Path

from _common import append_event, append_jsonl, ensure_case, next_id, split_csv, utc_now


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", type=Path, required=True)
    parser.add_argument("--obligation-id")
    parser.add_argument(
        "--category",
        choices=["contract", "proof", "audit", "computation", "formalization", "prior_art"],
        required=True,
    )
    parser.add_argument("--severity", choices=["fatal", "major", "minor", "editorial"], required=True)
    parser.add_argument(
        "--status",
        choices=["open", "in_progress", "resolved", "invalidated", "superseded"],
        default="open",
    )
    parser.add_argument("--claim-id")
    parser.add_argument("--audit-finding-id")
    parser.add_argument("--description", required=True)
    parser.add_argument("--required-resolution")
    parser.add_argument("--evidence-paths")
    parser.add_argument("--actor", default="root")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    case = ensure_case(args.case)
    ledger = case / "state" / "obligations.jsonl"
    obligation_id = args.obligation_id or next_id(ledger, "obligation_id", "OBL")
    now = utc_now()
    record = {
        "obligation_id": obligation_id,
        "category": args.category,
        "severity": args.severity,
        "status": args.status,
        "claim_id": args.claim_id,
        "audit_finding_id": args.audit_finding_id,
        "description": args.description,
        "required_resolution": split_csv(args.required_resolution),
        "evidence_paths": split_csv(args.evidence_paths),
        "created_at": now,
        "updated_at": now,
    }
    append_jsonl(ledger, record)
    affected = [obligation_id]
    for identifier in [args.claim_id, args.audit_finding_id]:
        if identifier:
            affected.append(identifier)
    append_event(
        case,
        actor=args.actor,
        action="obligation_recorded",
        affected_ids=affected,
        evidence_paths=record["evidence_paths"],
        details={"severity": args.severity, "status": args.status, "category": args.category},
    )
    print(obligation_id)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
