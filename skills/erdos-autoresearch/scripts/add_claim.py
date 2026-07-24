#!/usr/bin/env python3
"""Append a mathematical claim and its explicit dependencies."""

from __future__ import annotations

import argparse
from pathlib import Path

from _common import (
    append_event,
    append_jsonl,
    ensure_case,
    latest_by_id,
    load_json,
    next_id,
    read_jsonl,
    relative_to_case,
    resolve_case_path,
    split_csv,
    utc_now,
)


STATUSES = ["conjectured", "tested", "proved", "refuted", "machine_checked", "withdrawn"]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", type=Path, required=True)
    parser.add_argument("--claim-id")
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--statement")
    group.add_argument("--statement-file", type=Path)
    group.add_argument(
        "--affirmative-outcome",
        action="store_true",
        help="Use the exact affirmative statement from the audited contract.",
    )
    parser.add_argument("--status", choices=STATUSES, default="conjectured")
    parser.add_argument("--route-id")
    parser.add_argument("--dependencies")
    parser.add_argument("--external-dependencies")
    parser.add_argument("--proof-location")
    parser.add_argument("--counterexample-location")
    parser.add_argument("--machine-check")
    parser.add_argument("--actor", default="root")
    parser.add_argument("--allow-missing-dependencies", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    case = ensure_case(args.case)
    ledger = case / "state" / "claims.jsonl"
    claim_id = args.claim_id or next_id(ledger, "claim_id", "CLM")
    statement = args.statement
    if args.statement_file:
        statement = args.statement_file.read_text(encoding="utf-8").strip()
    role = "intermediate"
    if args.affirmative_outcome:
        contract = load_json(case / "contract" / "problem_contract.json")
        affirmative = contract.get("allowed_outcomes", {}).get("affirmative", {})
        statement = affirmative.get("statement")
        if affirmative.get("enabled") is not True or not isinstance(statement, str):
            raise SystemExit("The contract has no enabled affirmative outcome")
        if not statement.strip():
            raise SystemExit("The contract affirmative statement is empty")
        role = "final_affirmative"
    assert statement is not None

    dependencies = split_csv(args.dependencies)
    current = latest_by_id(read_jsonl(ledger), "claim_id")
    missing = [dep for dep in dependencies if dep not in current and dep != claim_id]
    if missing and not args.allow_missing_dependencies:
        raise SystemExit(f"Missing internal dependencies: {', '.join(missing)}")
    if claim_id in dependencies:
        raise SystemExit("A claim may not depend directly on itself")

    if args.status == "proved" and not args.proof_location:
        raise SystemExit("A proved claim requires --proof-location")
    if args.status == "refuted" and not args.counterexample_location:
        raise SystemExit("A refuted claim requires --counterexample-location")
    if args.status == "machine_checked" and not args.machine_check:
        raise SystemExit("A machine_checked claim requires --machine-check")

    evidence_values = {
        "proof_location": args.proof_location,
        "counterexample_location": args.counterexample_location,
        "machine_check": args.machine_check,
    }
    normalized_evidence: dict[str, str | None] = {}
    for field, value in evidence_values.items():
        if value is None:
            normalized_evidence[field] = None
            continue
        path = resolve_case_path(case, value, must_exist=True, nonempty=True)
        normalized_evidence[field] = relative_to_case(case, path)

    now = utc_now()
    record = {
        "claim_id": claim_id,
        "statement": statement,
        "role": role,
        "status": args.status,
        "route_id": args.route_id,
        "dependencies": dependencies,
        "external_dependencies": split_csv(args.external_dependencies),
        **normalized_evidence,
        "created_at": now,
        "updated_at": now,
    }
    append_jsonl(ledger, record)
    evidence = [
        path
        for path in normalized_evidence.values()
        if path
    ]
    append_event(
        case,
        actor=args.actor,
        action="claim_recorded",
        affected_ids=[claim_id, *dependencies],
        evidence_paths=evidence,
        details={"status": args.status, "role": role, "route_id": args.route_id},
    )
    print(claim_id)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
