#!/usr/bin/env python3
"""Render a concise Markdown status dashboard from canonical state."""

from __future__ import annotations

import argparse
from collections import Counter
from pathlib import Path

from _common import atomic_write_text, ensure_case, latest_by_id, load_json, read_jsonl, utc_now


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", type=Path, required=True)
    return parser.parse_args()


def table(counter: Counter[str]) -> str:
    if not counter:
        return "_None_\n"
    rows = ["| Status | Count |", "|---|---:|"]
    rows.extend(f"| {key} | {value} |" for key, value in sorted(counter.items()))
    return "\n".join(rows) + "\n"


def main() -> int:
    args = parse_args()
    case = ensure_case(args.case)
    config = load_json(case / "run_config.json")
    checkpoint = load_json(case / "state" / "checkpoint.json")
    routes = latest_by_id(read_jsonl(case / "state" / "approach_registry.jsonl"), "route_id")
    claims = latest_by_id(read_jsonl(case / "state" / "claims.jsonl"), "claim_id")
    obligations = latest_by_id(read_jsonl(case / "state" / "obligations.jsonl"), "obligation_id")
    findings = latest_by_id(read_jsonl(case / "state" / "audit_findings.jsonl"), "finding_id")

    route_status = Counter(item.get("status", "unknown") for item in routes.values())
    route_family = Counter(item.get("family", "unknown") for item in routes.values())
    claim_status = Counter(item.get("status", "unknown") for item in claims.values())
    open_obligations = [
        item for item in obligations.values() if item.get("status") in {"open", "in_progress"}
    ]
    open_findings = [
        item for item in findings.values() if item.get("status") in {"open", "in_progress"}
    ]

    lines = [
        f"# Research status — {config.get('title')}",
        "",
        f"- Case ID: `{config.get('case_id')}`",
        f"- Generated: `{utc_now()}`",
        f"- Phase: `{checkpoint.get('phase')}`",
        f"- Round: `{checkpoint.get('round')}`",
        f"- Stagnant rounds: `{checkpoint.get('stagnant_rounds')}`",
        f"- Active candidate claim: `{checkpoint.get('active_candidate_claim')}`",
        "",
        "## Route status",
        "",
        table(route_status),
        "## Route families",
        "",
        table(route_family),
        "## Claim status",
        "",
        table(claim_status),
        "## Open substantive obligations",
        "",
    ]
    if open_obligations:
        lines.extend(["| ID | Severity | Category | Claim | Description |", "|---|---|---|---|---|"])
        for item in sorted(
            open_obligations,
            key=lambda x: ({"fatal": 0, "major": 1, "minor": 2, "editorial": 3}.get(x.get("severity"), 9), x.get("obligation_id", "")),
        ):
            description = str(item.get("description", "")).replace("|", "\\|")
            lines.append(
                f"| {item.get('obligation_id')} | {item.get('severity')} | "
                f"{item.get('category')} | {item.get('claim_id') or ''} | {description} |"
            )
    else:
        lines.append("_None_")

    lines.extend(["", "## Open audit findings", ""])
    if open_findings:
        lines.extend(["| ID | Severity | Lane | Claim | Issue |", "|---|---|---|---|---|"])
        for item in open_findings:
            issue = str(item.get("issue", "")).replace("|", "\\|")
            lines.append(
                f"| {item.get('finding_id')} | {item.get('severity')} | "
                f"{item.get('lane')} | {item.get('claim_id') or ''} | {issue} |"
            )
    else:
        lines.append("_None_")

    lines.extend(["", "## Next actions", ""])
    for action in checkpoint.get("next_actions", []):
        lines.append(f"- {action}")
    lines.append("")

    atomic_write_text(case / "STATUS.md", "\n".join(lines))
    print(case / "STATUS.md")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
