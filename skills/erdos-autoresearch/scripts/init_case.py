#!/usr/bin/env python3
"""Initialize a durable autonomous-mathematics research case."""

from __future__ import annotations

import argparse
import shutil
from pathlib import Path

from _common import AUDIT_LANES, append_event, utc_now, write_json


DIRECTORIES = [
    "source",
    "contract",
    "state",
    "routes",
    "claims",
    "experiments",
    "proof",
    "audit",
    "formal",
    "scratch",
    "release",
]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case-id", required=True)
    parser.add_argument("--title", required=True)
    parser.add_argument("--problem-file", type=Path)
    parser.add_argument("--base", type=Path, default=Path("cases"))
    parser.add_argument(
        "--literature-mode",
        choices=["benchmark_blind", "background_only", "full_research"],
        default="background_only",
    )
    parser.add_argument(
        "--selection-mode", choices=["specified", "autonomous"], default="specified"
    )
    parser.add_argument("--minimum-research-hours", type=float, default=8.0)
    parser.add_argument("--strategy-reset-rounds", type=int, default=40)
    parser.add_argument("--maximum-active-routes", type=int, default=12)
    parser.add_argument("--force", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.minimum_research_hours < 8:
        raise SystemExit("--minimum-research-hours must be at least 8")
    if args.strategy_reset_rounds < 1:
        raise SystemExit("--strategy-reset-rounds must be positive")
    case = (args.base / args.case_id).resolve()
    if case.exists() and any(case.iterdir()) and not args.force:
        raise SystemExit(f"Refusing to overwrite non-empty case: {case}")
    case.mkdir(parents=True, exist_ok=True)
    for directory in DIRECTORIES:
        (case / directory).mkdir(parents=True, exist_ok=True)

    config = {
        "schema_version": 1,
        "case_id": args.case_id,
        "title": args.title,
        "selection_mode": args.selection_mode,
        "literature_mode": args.literature_mode,
        "target_mode": "prove",
        "computation": {
            "allowed": True,
            "exact_arithmetic_preferred": True,
            "require_reproducibility": True,
        },
        "formalization": {"system": "lean", "required": False},
        "budget": {
            "minimum_research_hours": args.minimum_research_hours,
            "strategy_reset_rounds": args.strategy_reset_rounds,
            "maximum_active_routes": args.maximum_active_routes,
            "maximum_stagnant_rounds": 5,
            "probe_rounds": 2,
        },
        "release": {
            "require_clean_room_audit": True,
            "require_prior_art_audit": True,
            "require_reproducible_experiments": True,
            "required_audit_lanes": AUDIT_LANES,
        },
        "created_at": utc_now(),
    }
    write_json(case / "run_config.json", config)

    contract = {
        "schema_version": 1,
        "case_id": args.case_id,
        "source": {
            "uri": "",
            "sha256": "",
            "retrieved_at": "",
            "published_or_updated_at": None,
        },
        "canonical_statement": "TODO",
        "interpretations": [],
        "definitions": [],
        "quantifier_matrix": [],
        "allowed_outcomes": {
            "affirmative": {"enabled": True, "statement": "TODO", "obligations": []},
            "negative": {
                "enabled": False,
                "statement": (
                    "Counterexamples are diagnostic tools for intermediate claims, "
                    "not a terminal outcome."
                ),
                "obligations": [],
            },
        },
        "non_solutions": [],
        "traps": [],
        "edge_cases": [],
        "external_theorem_policy": [],
        "release_obligations": [
            "statement_fidelity",
            "logical_closure",
            "external_theorem_applicability",
            "edge_cases",
            "circularity",
            "computational_reproducibility",
            "formalization_scope",
            "prior_art",
        ],
        "semantic_audits": [],
    }
    write_json(case / "contract" / "problem_contract.json", contract)
    write_json(
        case / "state" / "checkpoint.json",
        {
            "phase": "INITIALIZED",
            "round": 0,
            "stagnant_rounds": 0,
            "last_progress_at": utc_now(),
            "active_candidate_claim": None,
            "next_actions": ["Freeze exact source statement", "Compile proof contract"],
        },
    )
    write_json(case / "state" / "claim_graph.json", {"nodes": [], "edges": []})
    write_json(
        case / "state" / "task_queue.json", {"generated_at": utc_now(), "tasks": []}
    )
    write_json(
        case / "formal" / "verification_manifest.json",
        {
            "schema_version": 1,
            "case_id": args.case_id,
            "toolchain": [],
            "final_theorem": {
                "status": "not_checked",
                "declaration": None,
                "file": None,
                "trust_base": [],
            },
            "items": [],
            "admitted_or_unsafe": [],
        },
    )

    for ledger in [
        "approach_registry.jsonl",
        "claims.jsonl",
        "obligations.jsonl",
        "audit_findings.jsonl",
        "audits.jsonl",
        "counterexamples.jsonl",
        "experiments.jsonl",
        "external_theorems.jsonl",
        "events.jsonl",
    ]:
        (case / "state" / ledger).touch(exist_ok=True)

    if args.problem_file:
        if not args.problem_file.exists():
            raise SystemExit(f"Problem file not found: {args.problem_file}")
        shutil.copy2(args.problem_file, case / "source" / "unfrozen_input.md")

    append_event(case, actor="init_case.py", action="case_initialized")
    print(case)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
