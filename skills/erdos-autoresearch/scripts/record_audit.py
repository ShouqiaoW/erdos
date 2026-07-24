#!/usr/bin/env python3
"""Record a completed audit lane against the current frozen candidate."""

from __future__ import annotations

import argparse
from pathlib import Path

from _common import (
    AUDIT_LANES,
    append_event,
    append_jsonl,
    ensure_case,
    load_json,
    next_id,
    relative_to_case,
    resolve_case_path,
    sha256_file,
    utc_now,
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", type=Path, required=True)
    parser.add_argument("--lane", choices=AUDIT_LANES, required=True)
    parser.add_argument("--auditor", required=True)
    parser.add_argument("--status", choices=["pass", "fail"], required=True)
    parser.add_argument("--report-path", required=True)
    parser.add_argument(
        "--independent",
        action="store_true",
        help="Attest that the auditor was isolated from discovery and repair context.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    case = ensure_case(args.case)
    if not args.auditor.strip():
        raise SystemExit("Auditor identity must be non-empty")

    freeze = load_json(case / "audit" / "candidate_freeze.json")
    generation = freeze.get("generation")
    final_claim = freeze.get("final_claim")
    if not isinstance(generation, int) or generation < 1:
        raise SystemExit("Candidate freeze has no valid generation")
    if not isinstance(final_claim, str) or not final_claim:
        raise SystemExit("Candidate freeze has no final claim")

    report = resolve_case_path(
        case,
        args.report_path,
        must_exist=True,
        nonempty=True,
    )
    report_path = relative_to_case(case, report)
    ledger = case / "state" / "audits.jsonl"
    audit_id = next_id(ledger, "audit_id", "AUDIT")
    record = {
        "audit_id": audit_id,
        "lane": args.lane,
        "candidate_generation": generation,
        "final_claim": final_claim,
        "auditor": args.auditor,
        "independent": args.independent,
        "status": args.status,
        "report_path": report_path,
        "report_sha256": sha256_file(report),
        "completed_at": utc_now(),
    }
    append_jsonl(ledger, record)
    append_event(
        case,
        actor=args.auditor,
        action="audit_lane_completed",
        affected_ids=[audit_id, final_claim],
        evidence_paths=[report_path],
        details={
            "lane": args.lane,
            "status": args.status,
            "candidate_generation": generation,
            "independent": args.independent,
        },
    )
    print(audit_id)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
