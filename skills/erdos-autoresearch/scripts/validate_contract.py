#!/usr/bin/env python3
"""Validate the minimum semantic and structural requirements of a proof contract."""

from __future__ import annotations

import argparse
from pathlib import Path
from typing import Any

from _common import (
    ensure_case,
    has_placeholder,
    load_json,
    sha256_file,
    write_json,
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", type=Path, required=True)
    parser.add_argument("--allow-draft", action="store_true")
    parser.add_argument("--report")
    return parser.parse_args()


def require_list(
    contract: dict[str, Any], key: str, errors: list[str], minimum: int = 0
) -> list[Any]:
    value = contract.get(key)
    if not isinstance(value, list):
        errors.append(f"{key} must be a list")
        return []
    if len(value) < minimum:
        errors.append(f"{key} must contain at least {minimum} item(s)")
    return value


def validate(case: Path, allow_draft: bool) -> dict[str, Any]:
    errors: list[str] = []
    warnings: list[str] = []
    contract = load_json(case / "contract" / "problem_contract.json")
    source_path = case / "source" / "original_statement.md"
    provenance_path = case / "source" / "provenance.json"

    if not source_path.exists():
        errors.append("Frozen source statement is missing")
    if not provenance_path.exists():
        errors.append("Source provenance is missing")

    if source_path.exists():
        actual_hash = sha256_file(source_path)
        contract_hash = contract.get("source", {}).get("sha256")
        if actual_hash != contract_hash:
            errors.append("Contract source hash does not match frozen statement")

    if contract.get("schema_version") != 1:
        errors.append("Unsupported schema_version")
    canonical = contract.get("canonical_statement")
    if not isinstance(canonical, str) or not canonical.strip():
        errors.append("canonical_statement is required")

    definitions = require_list(contract, "definitions", errors)
    quantifiers = require_list(contract, "quantifier_matrix", errors)
    non_solutions = require_list(contract, "non_solutions", errors, minimum=1)
    traps = require_list(contract, "traps", errors, minimum=1)
    require_list(contract, "edge_cases", errors)
    audits = require_list(contract, "semantic_audits", errors, minimum=2)

    ids: set[str] = set()
    for collection_name, collection in [
        ("definitions", definitions),
        ("quantifier_matrix", quantifiers),
        ("traps", traps),
    ]:
        for item in collection:
            if isinstance(item, dict) and isinstance(item.get("id"), str):
                if item["id"] in ids:
                    errors.append(f"Duplicate ID {item['id']} in {collection_name}")
                ids.add(item["id"])

    outcomes = contract.get("allowed_outcomes")
    if not isinstance(outcomes, dict):
        errors.append("allowed_outcomes must be an object")
    else:
        affirmative = outcomes.get("affirmative")
        if not isinstance(affirmative, dict):
            errors.append("allowed_outcomes.affirmative must be an object")
        else:
            if affirmative.get("enabled") is not True:
                errors.append("Affirmative outcome must be enabled")
            if (
                not isinstance(affirmative.get("statement"), str)
                or not affirmative["statement"].strip()
            ):
                errors.append("Affirmative outcome requires a statement")
            obligations = affirmative.get("obligations")
            if not isinstance(obligations, list) or not obligations:
                errors.append("Affirmative outcome requires obligations")

        negative = outcomes.get("negative")
        if not isinstance(negative, dict):
            errors.append("allowed_outcomes.negative must be an object")
        else:
            if negative.get("enabled") is not False:
                errors.append(
                    "Negative outcome must remain disabled under the "
                    "affirmative-proof research contract"
                )
            if negative.get("obligations") not in ([], None):
                errors.append("Disabled negative outcome must not contain obligations")

    for index, audit in enumerate(audits):
        if not isinstance(audit, dict):
            errors.append(f"semantic_audits[{index}] must be an object")
            continue
        if audit.get("status") not in {"pass", "fail"}:
            errors.append(f"semantic_audits[{index}].status must be pass or fail")
        if not audit.get("auditor"):
            errors.append(f"semantic_audits[{index}].auditor is required")
    if any(isinstance(a, dict) and a.get("status") == "fail" for a in audits):
        errors.append("At least one semantic audit failed")

    if has_placeholder(contract):
        message = "Contract still contains TODO or REPLACE_ME placeholders"
        if allow_draft:
            warnings.append(message)
        else:
            errors.append(message)

    if len(definitions) == 0:
        warnings.append("Definition ledger is empty")
    if len(quantifiers) == 0:
        warnings.append(
            "Quantifier matrix is empty; confirm this is genuinely quantifier-free"
        )
    if len(non_solutions) < 3:
        warnings.append("Non-solution list is unusually short")
    if len(traps) < 3:
        warnings.append("Trap list is unusually short")

    report = {
        "valid": not errors,
        "errors": errors,
        "warnings": warnings,
        "contract_path": "contract/problem_contract.json",
    }
    return report


def main() -> int:
    args = parse_args()
    case = ensure_case(args.case)
    report = validate(case, args.allow_draft)
    report_path = (
        Path(args.report)
        if args.report
        else case / "contract" / "validation_report.json"
    )
    write_json(report_path, report)
    for error in report["errors"]:
        print(f"ERROR: {error}")
    for warning in report["warnings"]:
        print(f"WARNING: {warning}")
    print("VALID" if report["valid"] else "INVALID")
    return 0 if report["valid"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
