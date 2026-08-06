#!/usr/bin/env python3
"""Append or update an approach route in the canonical registry."""

from __future__ import annotations

import argparse
from pathlib import Path

from _common import append_event, append_jsonl, ensure_case, next_id, split_csv, utc_now


STATUSES = ["proposed", "active", "blocked", "refuted", "merged", "completed", "abandoned"]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", type=Path, required=True)
    parser.add_argument("--route-id")
    parser.add_argument("--family", required=True)
    parser.add_argument("--mechanism", required=True)
    parser.add_argument("--status", choices=STATUSES, default="proposed")
    parser.add_argument("--claims-produced")
    parser.add_argument("--blocker")
    parser.add_argument("--reopen-condition")
    parser.add_argument("--falsification-attempts")
    parser.add_argument("--evidence-paths")
    parser.add_argument("--actor", default="root")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    case = ensure_case(args.case)
    ledger = case / "state" / "approach_registry.jsonl"
    route_id = args.route_id or next_id(ledger, "route_id", "ROUTE")
    now = utc_now()
    record = {
        "route_id": route_id,
        "family": args.family,
        "mechanism": args.mechanism,
        "status": args.status,
        "claims_produced": split_csv(args.claims_produced),
        "blocker": args.blocker,
        "reopen_condition": args.reopen_condition,
        "falsification_attempts": split_csv(args.falsification_attempts),
        "evidence_paths": split_csv(args.evidence_paths),
        "created_at": now,
        "updated_at": now,
    }
    append_jsonl(ledger, record)
    append_event(
        case,
        actor=args.actor,
        action="route_recorded",
        affected_ids=[route_id],
        evidence_paths=record["evidence_paths"],
        details={"status": args.status, "family": args.family},
    )
    print(route_id)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
