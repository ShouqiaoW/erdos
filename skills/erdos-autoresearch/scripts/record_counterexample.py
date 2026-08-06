#!/usr/bin/env python3
"""Record a candidate or verified counterexample in the canonical ledger."""

from __future__ import annotations

import argparse
from pathlib import Path

from _common import append_event, append_jsonl, ensure_case, next_id, split_csv, utc_now


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", type=Path, required=True)
    parser.add_argument("--counterexample-id")
    parser.add_argument("--claim-id", required=True)
    parser.add_argument("--status", choices=["candidate", "verified", "invalidated"], default="candidate")
    parser.add_argument("--description", required=True)
    parser.add_argument("--object-path")
    parser.add_argument("--verification")
    parser.add_argument("--experiment-ids")
    parser.add_argument("--evidence-paths")
    parser.add_argument("--actor", default="counterexample_hunter")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    case = ensure_case(args.case)
    ledger = case / "state" / "counterexamples.jsonl"
    counterexample_id = args.counterexample_id or next_id(
        ledger, "counterexample_id", "CTR"
    )
    now = utc_now()
    evidence = split_csv(args.evidence_paths)
    if args.object_path:
        evidence.append(args.object_path)
    record = {
        "counterexample_id": counterexample_id,
        "claim_id": args.claim_id,
        "status": args.status,
        "description": args.description,
        "object_path": args.object_path,
        "verification": args.verification,
        "experiment_ids": split_csv(args.experiment_ids),
        "evidence_paths": evidence,
        "created_at": now,
        "updated_at": now,
    }
    append_jsonl(ledger, record)
    append_event(
        case,
        actor=args.actor,
        action="counterexample_recorded",
        affected_ids=[
            counterexample_id,
            args.claim_id,
            *record["experiment_ids"],
        ],
        evidence_paths=evidence,
        details={"status": args.status},
    )
    print(counterexample_id)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
