#!/usr/bin/env python3
"""Record an adversarial finding and create a linked obligation when substantive."""

from __future__ import annotations

import argparse
from pathlib import Path

from _common import (
    AUDIT_LANES,
    append_event,
    append_jsonl,
    ensure_case,
    next_id,
    split_csv,
    utc_now,
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", type=Path, required=True)
    parser.add_argument("--finding-id")
    parser.add_argument(
        "--lane",
        choices=AUDIT_LANES,
        required=True,
    )
    parser.add_argument(
        "--severity",
        choices=["fatal", "major", "minor", "editorial"],
        required=True,
    )
    parser.add_argument(
        "--status",
        choices=["open", "in_progress", "resolved", "invalidated", "superseded"],
        default="open",
    )
    parser.add_argument("--claim-id")
    parser.add_argument("--proof-location")
    parser.add_argument("--issue", required=True)
    parser.add_argument("--required-resolution")
    parser.add_argument("--evidence-paths")
    parser.add_argument("--actor", default="hostile_referee")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    case = ensure_case(args.case)
    findings = case / "state" / "audit_findings.jsonl"
    finding_id = args.finding_id or next_id(findings, "finding_id", "AUD")
    now = utc_now()
    record = {
        "finding_id": finding_id,
        "lane": args.lane,
        "severity": args.severity,
        "status": args.status,
        "claim_id": args.claim_id,
        "proof_location": args.proof_location,
        "issue": args.issue,
        "required_resolution": split_csv(args.required_resolution),
        "evidence_paths": split_csv(args.evidence_paths),
        "created_at": now,
        "updated_at": now,
    }
    append_jsonl(findings, record)

    affected = [finding_id]
    if args.claim_id:
        affected.append(args.claim_id)

    obligation_id = None
    if args.severity in {"fatal", "major"} and args.status in {"open", "in_progress"}:
        obligations = case / "state" / "obligations.jsonl"
        obligation_id = next_id(obligations, "obligation_id", "OBL")
        append_jsonl(
            obligations,
            {
                "obligation_id": obligation_id,
                "category": "audit",
                "severity": args.severity,
                "status": "open",
                "claim_id": args.claim_id,
                "audit_finding_id": finding_id,
                "description": args.issue,
                "required_resolution": record["required_resolution"],
                "evidence_paths": record["evidence_paths"],
                "created_at": now,
                "updated_at": now,
            },
        )
        affected.append(obligation_id)

    append_event(
        case,
        actor=args.actor,
        action="audit_finding_recorded",
        affected_ids=affected,
        evidence_paths=record["evidence_paths"],
        details={"lane": args.lane, "severity": args.severity, "status": args.status},
    )
    print(finding_id)
    if obligation_id:
        print(obligation_id)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
