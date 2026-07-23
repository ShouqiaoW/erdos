#!/usr/bin/env python3
"""Conservative release gate for candidate mathematical research packages."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from _common import (
    AUDIT_LANES,
    ResearchStateError,
    ensure_case,
    latest_by_id,
    load_json,
    read_jsonl,
    resolve_case_path,
    sha256_file,
    write_json,
)
from freeze_candidate import STATIC_FREEZE_ARTIFACTS
from validate_claim_graph import validate as validate_graph
from validate_contract import validate as validate_contract


ALLOWED_AUTOMATED_STATUSES = {
    "INTERNALLY_AUDITED_CANDIDATE",
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", type=Path, required=True)
    parser.add_argument(
        "--status", required=True, choices=sorted(ALLOWED_AUTOMATED_STATUSES)
    )
    parser.add_argument("--final-claim", required=True)
    return parser.parse_args()


def exists_nonempty(path: Path) -> bool:
    return path.exists() and path.is_file() and path.stat().st_size > 0


def parse_timestamp(value: Any) -> datetime | None:
    if not isinstance(value, str) or not value.strip():
        return None
    try:
        parsed = datetime.fromisoformat(value.replace("Z", "+00:00"))
    except ValueError:
        return None
    if parsed.tzinfo is None:
        parsed = parsed.replace(tzinfo=timezone.utc)
    return parsed.astimezone(timezone.utc)


def expected_frozen_paths(case: Path, final_claim: str) -> tuple[set[str], list[str]]:
    expected = {
        "proof/candidate_proof.tex",
        *STATIC_FREEZE_ARTIFACTS.values(),
    }
    errors: list[str] = []
    claims = latest_by_id(
        read_jsonl(case / "state" / "claims.jsonl"),
        "claim_id",
    )
    external = latest_by_id(
        read_jsonl(case / "state" / "external_theorems.jsonl"),
        "theorem_id",
    )
    reachable: set[str] = set()
    pending = [final_claim]
    while pending:
        claim_id = pending.pop()
        if claim_id in reachable:
            continue
        claim = claims.get(claim_id)
        if claim is None:
            errors.append(f"Final dependency cone is missing {claim_id}")
            continue
        reachable.add(claim_id)
        pending.extend(claim.get("dependencies", []))

    for claim_id in sorted(reachable):
        claim = claims[claim_id]
        evidence_field = {
            "proved": "proof_location",
            "machine_checked": "machine_check",
        }.get(str(claim.get("status")))
        if evidence_field:
            evidence = claim.get(evidence_field)
            if isinstance(evidence, str) and evidence:
                try:
                    path = resolve_case_path(
                        case,
                        evidence,
                        must_exist=True,
                        nonempty=True,
                    )
                except ResearchStateError as exc:
                    errors.append(f"{claim_id}: {exc}")
                else:
                    expected.add(str(path.relative_to(case)))
        for theorem_id in claim.get("external_dependencies", []):
            theorem = external.get(theorem_id)
            if theorem is None:
                continue
            evidence = theorem.get("evidence_path")
            if isinstance(evidence, str) and evidence:
                try:
                    path = resolve_case_path(
                        case,
                        evidence,
                        must_exist=True,
                        nonempty=True,
                    )
                except ResearchStateError as exc:
                    errors.append(f"{theorem_id}: {exc}")
                else:
                    expected.add(str(path.relative_to(case)))

    for experiment in read_jsonl(case / "state" / "experiments.jsonl"):
        if experiment.get("release_relevant") is not True:
            continue
        experiment_id = experiment.get("experiment_id")
        if not isinstance(experiment_id, str) or not experiment_id:
            errors.append("Release-relevant experiment has no experiment_id")
            continue
        expected.update(
            {
                f"experiments/{experiment_id}/manifest.json",
                f"experiments/{experiment_id}/stdout.txt",
                f"experiments/{experiment_id}/stderr.txt",
            }
        )
        source_hashes = experiment.get("source_hashes", {})
        if not isinstance(source_hashes, dict):
            errors.append(
                f"Release-relevant experiment {experiment_id} has malformed "
                "source_hashes"
            )
            continue
        for source_path in source_hashes:
            try:
                path = resolve_case_path(
                    case,
                    str(source_path),
                    must_exist=True,
                    nonempty=True,
                )
            except ResearchStateError as exc:
                errors.append(f"{experiment_id}: {exc}")
            else:
                expected.add(str(path.relative_to(case)))

    if (case / "proof" / "candidate_proof.pdf").exists():
        expected.add("proof/candidate_proof.pdf")
    return expected, errors


def main() -> int:
    args = parse_args()
    case = ensure_case(args.case)
    config = load_json(case / "run_config.json")
    failures: list[str] = []
    warnings: list[str] = []

    contract_report = validate_contract(case, allow_draft=False)
    if not contract_report["valid"]:
        failures.extend(f"Contract: {item}" for item in contract_report["errors"])

    graph_report = validate_graph(case, args.final_claim)
    if not graph_report["valid"]:
        failures.extend(f"Claim graph: {item}" for item in graph_report["errors"])

    if config.get("target_mode") != "prove":
        failures.append("Run config target_mode must remain prove")
    for flag in [
        "require_clean_room_audit",
        "require_prior_art_audit",
        "require_reproducible_experiments",
    ]:
        if config.get("release", {}).get(flag) is not True:
            failures.append(f"Run config release.{flag} must remain true")

    minimum_hours = config.get("budget", {}).get("minimum_research_hours")
    elapsed_hours: float | None = None
    if not isinstance(minimum_hours, (int, float)) or minimum_hours < 8:
        failures.append("Run config must require at least eight research hours")
    else:
        started_at = parse_timestamp(config.get("created_at"))
        if started_at is None:
            failures.append("Run config has no valid created_at timestamp")
        else:
            elapsed_hours = (
                datetime.now(timezone.utc) - started_at
            ).total_seconds() / 3600
            if elapsed_hours < minimum_hours:
                failures.append(
                    "Minimum research duration not met: "
                    f"{elapsed_hours:.2f}h elapsed, {minimum_hours:g}h required"
                )

    obligations = latest_by_id(
        read_jsonl(case / "state" / "obligations.jsonl"), "obligation_id"
    )
    findings = latest_by_id(
        read_jsonl(case / "state" / "audit_findings.jsonl"), "finding_id"
    )

    open_substantive_obligations = [
        item
        for item in obligations.values()
        if item.get("status") in {"open", "in_progress"}
        and item.get("severity") in {"fatal", "major"}
    ]
    open_substantive_findings = [
        item
        for item in findings.values()
        if item.get("status") in {"open", "in_progress"}
        and item.get("severity") in {"fatal", "major"}
    ]
    if open_substantive_obligations:
        failures.append(
            f"{len(open_substantive_obligations)} fatal/major obligation(s) remain open"
        )
    if open_substantive_findings:
        failures.append(
            f"{len(open_substantive_findings)} fatal/major audit finding(s) remain open"
        )

    required_candidate_files = [
        case / "source" / "original_statement.md",
        case / "source" / "provenance.json",
        case / "contract" / "problem_contract.json",
        case / "audit" / "audit_report.md",
        case / "audit" / "prior_art_report.md",
        case / "formal" / "verification_manifest.json",
        case / "release" / "README.md",
        case / "audit" / "candidate_freeze.json",
        case / "proof" / "candidate_proof.tex",
        case / "state" / "audits.jsonl",
    ]
    for path in required_candidate_files:
        if not exists_nonempty(path):
            failures.append(
                f"Required candidate artifact missing or empty: {path.relative_to(case)}"
            )

    freeze_path = case / "audit" / "candidate_freeze.json"
    freeze: dict[str, Any] | None = None
    if freeze_path.exists():
        freeze = load_json(freeze_path)
        if freeze.get("candidate_kind") != "affirmative":
            failures.append("Candidate freeze must be affirmative")
        if freeze.get("final_claim") != args.final_claim:
            failures.append(
                "Candidate freeze final_claim does not match release final claim"
            )
        frozen_artifacts = freeze.get("artifacts")
        actual_frozen_paths: set[str] = set()
        if not isinstance(frozen_artifacts, dict):
            failures.append("Candidate freeze artifacts must be an object")
        else:
            for artifact in frozen_artifacts.values():
                if not isinstance(artifact, dict):
                    failures.append("Malformed candidate freeze artifact")
                    continue
                try:
                    artifact_path = resolve_case_path(
                        case,
                        str(artifact.get("path", "")),
                        must_exist=True,
                    )
                except ResearchStateError as exc:
                    failures.append(f"Invalid frozen artifact: {exc}")
                    continue
                actual_frozen_paths.add(str(artifact_path.relative_to(case)))
                if sha256_file(artifact_path) != artifact.get("sha256"):
                    failures.append(
                        f"Frozen artifact changed after audit: {artifact.get('path')}"
                    )
            expected_paths, expected_path_errors = expected_frozen_paths(
                case,
                args.final_claim,
            )
            failures.extend(
                f"Frozen artifact inventory: {error}"
                for error in expected_path_errors
            )
            for missing_path in sorted(expected_paths - actual_frozen_paths):
                failures.append(
                    f"Required frozen artifact omitted: {missing_path}"
                )

    required_lanes = config.get("release", {}).get(
        "required_audit_lanes",
        AUDIT_LANES,
    )
    if (
        not isinstance(required_lanes, list)
        or len(required_lanes) != len(AUDIT_LANES)
        or any(not isinstance(lane, str) for lane in required_lanes)
        or set(required_lanes) != set(AUDIT_LANES)
    ):
        failures.append(
            "Run config must require every standard adversarial audit lane"
        )
        required_lanes = AUDIT_LANES
    if (
        config.get("release", {}).get("require_clean_room_audit")
        and "clean_room" not in required_lanes
    ):
        failures.append("Clean-room audit is required but absent from audit lanes")

    audit_records = read_jsonl(case / "state" / "audits.jsonl")
    current_audits: dict[str, dict[str, Any]] = {}
    generation = freeze.get("generation") if freeze else None
    frozen_at = parse_timestamp(freeze.get("frozen_at")) if freeze else None
    if not isinstance(generation, int) or generation < 1:
        failures.append("Candidate freeze has no valid generation")
    else:
        for record in audit_records:
            if record.get("candidate_generation") == generation:
                lane = record.get("lane")
                if isinstance(lane, str):
                    current_audits[lane] = record

        for lane in required_lanes:
            record = current_audits.get(lane)
            if record is None:
                failures.append(
                    f"Required audit lane {lane} has no completion record "
                    f"for candidate generation {generation}"
                )
                continue
            if record.get("status") != "pass":
                failures.append(f"Required audit lane {lane} did not pass")
            if record.get("independent") is not True:
                failures.append(f"Required audit lane {lane} was not independent")
            if record.get("final_claim") != args.final_claim:
                failures.append(
                    f"Required audit lane {lane} targets a different final claim"
                )
            completed_at = parse_timestamp(record.get("completed_at"))
            if completed_at is None:
                failures.append(
                    f"Required audit lane {lane} has no valid completion time"
                )
            elif frozen_at is None or completed_at < frozen_at:
                failures.append(
                    f"Required audit lane {lane} predates the frozen candidate"
                )
            try:
                report_path = resolve_case_path(
                    case,
                    str(record.get("report_path", "")),
                    must_exist=True,
                    nonempty=True,
                )
            except ResearchStateError as exc:
                failures.append(f"Required audit lane {lane} has invalid report: {exc}")
                continue
            if sha256_file(report_path) != record.get("report_sha256"):
                failures.append(
                    f"Required audit lane {lane} report changed after completion"
                )

    if config.get("release", {}).get("require_prior_art_audit"):
        if not exists_nonempty(case / "audit" / "prior_art_report.md"):
            failures.append("Prior-art report missing")

    manifest_path = case / "formal" / "verification_manifest.json"
    if manifest_path.exists():
        manifest = load_json(manifest_path)
        if (
            manifest.get("admitted_or_unsafe")
            and manifest.get("final_theorem", {}).get("status") == "checked"
        ):
            failures.append(
                "Final theorem marked checked despite admitted_or_unsafe entries"
            )
    else:
        failures.append("Verification manifest missing")

    experiments = read_jsonl(case / "state" / "experiments.jsonl")
    if config.get("release", {}).get("require_reproducible_experiments"):
        for exp in experiments:
            if exp.get("release_relevant") is not True:
                continue
            if exp.get("return_code") not in {None, 0} or exp.get("timed_out"):
                failures.append(
                    f"Experiment {exp.get('experiment_id')} did not complete successfully"
                )
            if exp.get("record_only"):
                failures.append(
                    f"Experiment {exp.get('experiment_id')} was not executed"
                )
            if "TODO" in str(exp.get("interpretation", "")).upper():
                failures.append(
                    f"Experiment {exp.get('experiment_id')} lacks a precise interpretation"
                )
            if exp.get("reproduced_by_independent_checker") is not True:
                failures.append(
                    f"Experiment {exp.get('experiment_id')} lacks independent "
                    "reproduction"
                )
            experiment_id = exp.get("experiment_id")
            if isinstance(experiment_id, str):
                manifest_path = (
                    case / "experiments" / experiment_id / "manifest.json"
                )
                if not exists_nonempty(manifest_path):
                    failures.append(
                        f"Experiment {experiment_id} manifest is missing"
                    )
                else:
                    manifest = load_json(manifest_path)
                    if manifest != exp:
                        failures.append(
                            f"Experiment {experiment_id} ledger and manifest differ"
                        )
                for stream in ["stdout", "stderr"]:
                    stream_path = (
                        case / "experiments" / experiment_id / f"{stream}.txt"
                    )
                    if not stream_path.exists():
                        failures.append(
                            f"Experiment {experiment_id} {stream} is missing"
                        )
                    elif sha256_file(stream_path) != exp.get(
                        f"{stream}_sha256"
                    ):
                        failures.append(
                            f"Experiment {experiment_id} {stream} hash changed"
                        )
                source_hashes = exp.get("source_hashes", {})
                if not isinstance(source_hashes, dict):
                    failures.append(
                        f"Experiment {experiment_id} source_hashes is malformed"
                    )
                else:
                    for source_path, expected_hash in source_hashes.items():
                        try:
                            source = resolve_case_path(
                                case,
                                str(source_path),
                                must_exist=True,
                                nonempty=True,
                            )
                        except ResearchStateError as exc:
                            failures.append(
                                f"Experiment {experiment_id} has invalid source: {exc}"
                            )
                            continue
                        if sha256_file(source) != expected_hash:
                            failures.append(
                                f"Experiment {experiment_id} source hash changed: "
                                f"{source_path}"
                            )

    release_readme = case / "release" / "README.md"
    if release_readme.exists():
        text = release_readme.read_text(encoding="utf-8").lower()
        forbidden = [
            "problem solved",
            "conjecture solved",
            "proof accepted",
            "community accepted",
        ]
        for phrase in forbidden:
            if phrase in text:
                failures.append(
                    f"Release README contains forbidden status phrase: {phrase}"
                )

    report = {
        "passed": not failures,
        "status": args.status,
        "final_claim": args.final_claim,
        "minimum_research_hours": minimum_hours,
        "elapsed_research_hours": elapsed_hours,
        "failures": failures,
        "warnings": warnings,
        "contract_report": contract_report,
        "claim_graph_report": graph_report,
        "audit_lanes": {
            lane: {
                "audit_id": record.get("audit_id"),
                "status": record.get("status"),
                "report_path": record.get("report_path"),
                "report_sha256": record.get("report_sha256"),
            }
            for lane, record in current_audits.items()
        },
        "artifact_hashes": {
            str(path.relative_to(case)): sha256_file(path)
            for path in required_candidate_files
            if path.exists() and path.is_file()
        },
    }
    write_json(case / "release" / "gate_report.json", report)
    for failure in failures:
        print(f"FAIL: {failure}")
    print("PASS" if report["passed"] else "FAIL")
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
