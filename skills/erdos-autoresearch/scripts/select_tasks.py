#!/usr/bin/env python3
"""Generate a deterministic priority queue from current research state."""

from __future__ import annotations

import argparse
from collections import Counter
from pathlib import Path
from typing import Any

from _common import ensure_case, latest_by_id, read_jsonl, utc_now, write_json


SEVERITY_SCORE = {"fatal": 100, "major": 70, "minor": 25, "editorial": 5}
STATUS_SCORE = {"open": 20, "in_progress": 10}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", type=Path, required=True)
    parser.add_argument("--limit", type=int, default=8)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    case = ensure_case(args.case)
    routes = latest_by_id(
        read_jsonl(case / "state" / "approach_registry.jsonl"), "route_id"
    )
    claims = latest_by_id(read_jsonl(case / "state" / "claims.jsonl"), "claim_id")
    obligations = latest_by_id(
        read_jsonl(case / "state" / "obligations.jsonl"), "obligation_id"
    )

    family_counts = Counter(
        route.get("family", "unknown")
        for route in routes.values()
        if route.get("status") in {"proposed", "active"}
    )
    tasks: list[dict[str, Any]] = []

    for obligation_id, obligation in obligations.items():
        if obligation.get("status") not in {"open", "in_progress"}:
            continue
        severity = obligation.get("severity", "minor")
        score = SEVERITY_SCORE.get(severity, 0) + STATUS_SCORE.get(
            obligation.get("status"), 0
        )
        claim_id = obligation.get("claim_id")
        if claim_id and claim_id in claims:
            claim_status = claims[claim_id].get("status")
            if claim_status in {"conjectured", "tested"}:
                score += 15
        tasks.append(
            {
                "task_id": f"TASK-{obligation_id}",
                "kind": "resolve_obligation",
                "priority": score,
                "obligation_id": obligation_id,
                "claim_id": claim_id,
                "description": obligation.get("description"),
                "recommended_agent": (
                    "hostile_referee"
                    if obligation.get("category") == "audit"
                    else "lemma_prover"
                ),
            }
        )

    for route_id, route in routes.items():
        if route.get("status") not in {"proposed", "active"}:
            continue
        family = route.get("family", "unknown")
        underrepresentation_bonus = max(0, 12 - 3 * family_counts[family])
        score = 30 + underrepresentation_bonus
        if route.get("status") == "proposed":
            score += 8
        tasks.append(
            {
                "task_id": f"TASK-{route_id}",
                "kind": "advance_route",
                "priority": score,
                "route_id": route_id,
                "family": family,
                "description": route.get("mechanism"),
                "recommended_agent": "approach_scout",
            }
        )

    for claim_id, claim in claims.items():
        if claim.get("status") not in {"conjectured", "tested"}:
            continue
        score = 45 if claim.get("status") == "conjectured" else 35
        tasks.append(
            {
                "task_id": f"TASK-{claim_id}",
                "kind": "prove_or_refute_claim",
                "priority": score,
                "claim_id": claim_id,
                "description": claim.get("statement"),
                "recommended_agents": ["lemma_prover", "counterexample_hunter"],
            }
        )

    active_families = set(family_counts)
    if not any(
        any(token in family.lower() for token in ["counter", "falsif"])
        for family in active_families
    ):
        tasks.append(
            {
                "task_id": "TASK-COUNTEREXAMPLE-LANE",
                "kind": "open_counterexample_lane",
                "priority": 55,
                "description": (
                    "Create an independent counterexample lane attacking "
                    "intermediate claims and favored routes."
                ),
                "recommended_agent": "counterexample_hunter",
            }
        )

    tasks.sort(key=lambda item: (-item["priority"], item["task_id"]))
    output = {
        "generated_at": utc_now(),
        "limit": args.limit,
        "tasks": tasks[: args.limit],
        "candidate_count": len(tasks),
    }
    write_json(case / "state" / "task_queue.json", output)
    print(case / "state" / "task_queue.json")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
