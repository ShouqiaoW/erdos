#!/usr/bin/env python3
"""Validate the packaged Skill, templates, scripts, and metadata."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

try:
    import tomllib
except ImportError:  # pragma: no cover
    tomllib = None


REQUIRED = [
    "SKILL.md",
    "agents/openai.yaml",
    "references/workflow.md",
    "references/proof-contract.md",
    "references/orchestration.md",
    "references/adversarial-audit.md",
    "references/release-policy.md",
    "references/openai-cdc-example-prompt.txt",
    "references/openai-cdc-example-notes.md",
    "assets/problem_contract.json",
    "assets/audit_run.json",
    "assets/external_theorem_record.json",
    "scripts/_common.py",
    "scripts/add_external_theorem.py",
    "scripts/init_case.py",
    "scripts/freeze_statement.py",
    "scripts/compile_research_prompt.py",
    "scripts/freeze_candidate.py",
    "scripts/validate_contract.py",
    "scripts/validate_claim_graph.py",
    "scripts/release_gate.py",
    "scripts/record_audit.py",
]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--skill-dir", type=Path, required=True)
    parser.add_argument("--project-root", type=Path)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    skill = args.skill_dir.resolve()
    errors: list[str] = []

    for relative in REQUIRED:
        path = skill / relative
        if not path.exists():
            errors.append(f"Missing required file: {relative}")

    skill_md = skill / "SKILL.md"
    if skill_md.exists():
        text = skill_md.read_text(encoding="utf-8")
        if not text.startswith("---\n"):
            errors.append("SKILL.md is missing YAML frontmatter")
        expected_name = skill.name
        if f"\nname: {expected_name}\n" not in text:
            errors.append(
                f"SKILL.md name must match its directory: expected {expected_name}"
            )
        if "\ndescription:" not in text:
            errors.append("SKILL.md is missing description")

    for path in sorted((skill / "assets").glob("*.json")):
        try:
            json.loads(path.read_text(encoding="utf-8"))
        except json.JSONDecodeError as exc:
            errors.append(f"Invalid JSON asset {path.name}: {exc}")

    for path in sorted((skill / "references" / "schemas").glob("*.json")):
        try:
            json.loads(path.read_text(encoding="utf-8"))
        except json.JSONDecodeError as exc:
            errors.append(f"Invalid JSON schema {path.name}: {exc}")

    for path in sorted((skill / "scripts").glob("*.py")):
        try:
            compile(path.read_text(encoding="utf-8"), str(path), "exec")
        except (OSError, SyntaxError) as exc:
            errors.append(f"Python compile failure {path.name}: {exc}")

    if args.project_root:
        agents = args.project_root.resolve() / ".codex" / "agents"
        if agents.exists() and tomllib:
            for path in sorted(agents.glob("*.toml")):
                try:
                    data = tomllib.loads(path.read_text(encoding="utf-8"))
                except Exception as exc:
                    errors.append(f"Invalid TOML {path.name}: {exc}")
                    continue
                for key in ["name", "description", "developer_instructions"]:
                    if not data.get(key):
                        errors.append(f"{path.name} missing required key {key}")

    if errors:
        for error in errors:
            print(f"ERROR: {error}")
        return 1
    print("Skill doctor passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
