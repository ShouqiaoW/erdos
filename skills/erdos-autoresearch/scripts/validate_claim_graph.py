#!/usr/bin/env python3
"""Validate claim dependencies, proof statuses, and graph acyclicity."""

from __future__ import annotations

import argparse
from collections import defaultdict, deque
from pathlib import Path
from typing import Any

from _common import (
    ResearchStateError,
    ensure_case,
    latest_by_id,
    load_json,
    read_jsonl,
    resolve_case_path,
    write_json,
)


CLOSED_STATUSES = {"proved", "machine_checked"}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", type=Path, required=True)
    parser.add_argument("--final-claim")
    return parser.parse_args()


def validate(case: Path, final_claim: str | None = None) -> dict[str, Any]:
    claims = latest_by_id(read_jsonl(case / "state" / "claims.jsonl"), "claim_id")
    external_theorems = latest_by_id(
        read_jsonl(case / "state" / "external_theorems.jsonl"),
        "theorem_id",
    )
    contract = load_json(case / "contract" / "problem_contract.json")
    affirmative_statement = (
        contract.get("allowed_outcomes", {})
        .get("affirmative", {})
        .get("statement")
    )
    errors: list[str] = []
    warnings: list[str] = []
    edges: list[dict[str, str]] = []
    adjacency: dict[str, list[str]] = defaultdict(list)

    for claim_id, claim in claims.items():
        deps = claim.get("dependencies", [])
        if not isinstance(deps, list):
            errors.append(f"{claim_id}: dependencies must be a list")
            continue
        for dep in deps:
            if dep not in claims:
                errors.append(f"{claim_id}: missing dependency {dep}")
                continue
            if dep == claim_id:
                errors.append(f"{claim_id}: direct self-dependency")
            adjacency[claim_id].append(dep)
            edges.append({"from": claim_id, "to": dep})

    color: dict[str, int] = {claim_id: 0 for claim_id in claims}
    stack: list[str] = []
    cycles: list[list[str]] = []

    def dfs(node: str) -> None:
        color[node] = 1
        stack.append(node)
        for dep in adjacency.get(node, []):
            if color.get(dep, 0) == 0:
                dfs(dep)
            elif color.get(dep) == 1:
                start = stack.index(dep)
                cycles.append(stack[start:] + [dep])
        stack.pop()
        color[node] = 2

    for node in claims:
        if color[node] == 0:
            dfs(node)

    for cycle in cycles:
        errors.append("Dependency cycle: " + " -> ".join(cycle))

    for claim_id, claim in claims.items():
        role = claim.get("role")
        if role not in {"intermediate", "final_affirmative"}:
            errors.append(f"{claim_id}: invalid or missing role {role}")
        if role == "final_affirmative" and claim.get("statement") != affirmative_statement:
            errors.append(
                f"{claim_id}: final affirmative statement does not exactly match "
                "the audited contract"
            )

        status = claim.get("status")
        if status == "proved" and not claim.get("proof_location"):
            errors.append(f"{claim_id}: proved without proof_location")
        if status == "machine_checked" and not claim.get("machine_check"):
            errors.append(f"{claim_id}: machine_checked without machine_check")
        if status == "refuted" and not claim.get("counterexample_location"):
            errors.append(f"{claim_id}: refuted without counterexample_location")

        evidence_field = {
            "proved": "proof_location",
            "machine_checked": "machine_check",
            "refuted": "counterexample_location",
        }.get(str(status))
        if evidence_field and claim.get(evidence_field):
            try:
                resolve_case_path(
                    case,
                    str(claim[evidence_field]),
                    must_exist=True,
                    nonempty=True,
                )
            except ResearchStateError as exc:
                errors.append(f"{claim_id}: invalid {evidence_field}: {exc}")

        external_dependencies = claim.get("external_dependencies", [])
        if not isinstance(external_dependencies, list):
            errors.append(f"{claim_id}: external_dependencies must be a list")
            external_dependencies = []
        for theorem_id in external_dependencies:
            theorem = external_theorems.get(theorem_id)
            if theorem is None:
                errors.append(f"{claim_id}: missing external theorem {theorem_id}")
                continue
            if status in CLOSED_STATUSES and theorem.get("status") != "verified":
                errors.append(
                    f"{claim_id}: closed claim depends on unverified external "
                    f"theorem {theorem_id}"
                )
            if theorem.get("status") == "verified":
                if not isinstance(theorem.get("statement"), str) or not theorem[
                    "statement"
                ].strip():
                    errors.append(f"{theorem_id}: verified without exact statement")
                if not isinstance(theorem.get("source_uri"), str) or not theorem[
                    "source_uri"
                ].strip():
                    errors.append(f"{theorem_id}: verified without source URI")
                if not isinstance(theorem.get("hypotheses"), list):
                    errors.append(f"{theorem_id}: hypotheses must be a list")
                if (
                    not isinstance(theorem.get("application_mapping"), list)
                    or not theorem["application_mapping"]
                ):
                    errors.append(
                        f"{theorem_id}: verified without an application mapping"
                    )
                try:
                    resolve_case_path(
                        case,
                        str(theorem.get("evidence_path", "")),
                        must_exist=True,
                        nonempty=True,
                    )
                except ResearchStateError as exc:
                    errors.append(f"{theorem_id}: invalid evidence_path: {exc}")

        if status in CLOSED_STATUSES:
            for dep in adjacency.get(claim_id, []):
                dep_status = claims[dep].get("status")
                if dep_status not in CLOSED_STATUSES:
                    errors.append(
                        f"{claim_id}: closed claim depends on {dep} with status {dep_status}"
                    )

    if final_claim:
        if final_claim not in claims:
            errors.append(f"Final claim not found: {final_claim}")
        else:
            final_status = claims[final_claim].get("status")
            final_role = claims[final_claim].get("role")
            final_statement = claims[final_claim].get("statement")
            if final_role != "final_affirmative":
                errors.append(
                    f"Final claim {final_claim} is not role final_affirmative"
                )
            if final_statement != affirmative_statement:
                errors.append(
                    f"Final claim {final_claim} does not exactly match the "
                    "contract affirmative outcome"
                )
            if final_status not in CLOSED_STATUSES:
                errors.append(
                    f"Final claim {final_claim} has non-closed status {final_status}"
                )

            reachable: set[str] = set()
            queue = deque([final_claim])
            while queue:
                current = queue.popleft()
                if current in reachable or current not in claims:
                    continue
                reachable.add(current)
                queue.extend(adjacency.get(current, []))
            for claim_id in sorted(reachable):
                if claims[claim_id].get("status") not in CLOSED_STATUSES:
                    errors.append(
                        f"Final dependency cone contains open claim {claim_id}"
                    )

    report = {
        "valid": not errors,
        "errors": errors,
        "warnings": warnings,
        "nodes": [
            {
                "claim_id": claim_id,
                "status": claim.get("status"),
                "route_id": claim.get("route_id"),
            }
            for claim_id, claim in claims.items()
        ],
        "edges": edges,
        "external_theorems": [
            {
                "theorem_id": theorem_id,
                "status": theorem.get("status"),
            }
            for theorem_id, theorem in external_theorems.items()
        ],
        "final_claim": final_claim,
    }
    return report


def main() -> int:
    args = parse_args()
    case = ensure_case(args.case)
    report = validate(case, args.final_claim)
    write_json(case / "state" / "claim_graph.json", report)
    for error in report["errors"]:
        print(f"ERROR: {error}")
    print("VALID" if report["valid"] else "INVALID")
    return 0 if report["valid"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
