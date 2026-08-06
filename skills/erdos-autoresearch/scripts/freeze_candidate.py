#!/usr/bin/env python3
"""Freeze an affirmative proof candidate before independent audit."""

from __future__ import annotations

import argparse
import shutil
from pathlib import Path

from _common import (
    append_event,
    ensure_case,
    latest_by_id,
    load_json,
    read_jsonl,
    relative_to_case,
    resolve_case_path,
    sha256_file,
    utc_now,
    write_json,
)
from validate_contract import validate as validate_contract
from validate_claim_graph import validate as validate_graph


STATIC_FREEZE_ARTIFACTS = {
    "run_config": "run_config.json",
    "source_statement": "source/original_statement.md",
    "source_provenance": "source/provenance.json",
    "problem_contract": "contract/problem_contract.json",
    "contract_validation": "contract/validation_report.json",
    "claims_ledger": "state/claims.jsonl",
    "claim_graph": "state/claim_graph.json",
    "external_theorems_ledger": "state/external_theorems.jsonl",
    "experiments_ledger": "state/experiments.jsonl",
    "counterexamples_ledger": "state/counterexamples.jsonl",
    "verification_manifest": "formal/verification_manifest.json",
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", type=Path, required=True)
    parser.add_argument("--proof-source", type=Path, required=True)
    parser.add_argument("--proof-pdf", type=Path)
    parser.add_argument("--final-claim", required=True)
    parser.add_argument(
        "--candidate-kind",
        choices=["affirmative"],
        required=True,
    )
    parser.add_argument("--force", action="store_true")
    return parser.parse_args()


def add_frozen_artifact(
    artifacts: dict[str, dict[str, str]],
    *,
    key: str,
    case: Path,
    path: Path,
) -> None:
    resolved = resolve_case_path(case, path, must_exist=True)
    if not resolved.is_file():
        raise SystemExit(f"Frozen artifact is not a file: {path}")
    relative = relative_to_case(case, resolved)
    if any(item["path"] == relative for item in artifacts.values()):
        return
    artifacts[key] = {
        "path": relative,
        "sha256": sha256_file(resolved),
    }


def freeze_dependency_cone(
    case: Path,
    final_claim: str,
    artifacts: dict[str, dict[str, str]],
) -> None:
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
            raise SystemExit(f"Final dependency cone is missing {claim_id}")
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
            if not isinstance(evidence, str) or not evidence:
                raise SystemExit(
                    f"{claim_id} has no {evidence_field} to freeze"
                )
            add_frozen_artifact(
                artifacts,
                key=f"{claim_id}_{evidence_field}",
                case=case,
                path=Path(evidence),
            )
        for theorem_id in claim.get("external_dependencies", []):
            theorem = external.get(theorem_id)
            if theorem is None:
                raise SystemExit(f"Missing external theorem {theorem_id}")
            evidence = theorem.get("evidence_path")
            if not isinstance(evidence, str) or not evidence:
                raise SystemExit(
                    f"External theorem {theorem_id} has no evidence to freeze"
                )
            add_frozen_artifact(
                artifacts,
                key=f"{theorem_id}_evidence",
                case=case,
                path=Path(evidence),
            )


def freeze_release_relevant_experiments(
    case: Path,
    artifacts: dict[str, dict[str, str]],
) -> None:
    experiments = read_jsonl(case / "state" / "experiments.jsonl")
    for experiment in experiments:
        if experiment.get("release_relevant") is not True:
            continue
        experiment_id = experiment.get("experiment_id")
        if not isinstance(experiment_id, str) or not experiment_id:
            raise SystemExit("Release-relevant experiment has no experiment_id")
        experiment_dir = case / "experiments" / experiment_id
        for filename in ["manifest.json", "stdout.txt", "stderr.txt"]:
            add_frozen_artifact(
                artifacts,
                key=f"{experiment_id}_{filename.replace('.', '_')}",
                case=case,
                path=experiment_dir / filename,
            )
        source_hashes = experiment.get("source_hashes", {})
        if not isinstance(source_hashes, dict):
            raise SystemExit(
                f"Release-relevant experiment {experiment_id} has malformed "
                "source_hashes"
            )
        for index, source_path in enumerate(sorted(source_hashes)):
            add_frozen_artifact(
                artifacts,
                key=f"{experiment_id}_source_{index + 1}",
                case=case,
                path=Path(source_path),
            )


def main() -> int:
    args = parse_args()
    case = ensure_case(args.case)
    source = args.proof_source.resolve()
    if not source.exists():
        raise SystemExit(f"Proof source not found: {source}")

    contract_report = validate_contract(case, allow_draft=False)
    if not contract_report["valid"]:
        raise SystemExit(
            "Problem contract is not releasable:\n- "
            + "\n- ".join(contract_report["errors"])
        )
    write_json(case / "contract" / "validation_report.json", contract_report)

    graph_report = validate_graph(case, args.final_claim)
    if not graph_report["valid"]:
        raise SystemExit(
            "Final claim graph is not releasable:\n- "
            + "\n- ".join(graph_report["errors"])
        )
    write_json(case / "state" / "claim_graph.json", graph_report)

    freeze_path = case / "audit" / "candidate_freeze.json"
    if freeze_path.exists() and not args.force:
        raise SystemExit(
            "A candidate is already frozen. Use --force only after recording why a "
            "new audit generation is required."
        )

    target_source = case / "proof" / "candidate_proof.tex"
    if source != target_source.resolve():
        shutil.copy2(source, target_source)

    artifacts: dict[str, dict[str, str]] = {}
    add_frozen_artifact(
        artifacts,
        key="proof_source",
        case=case,
        path=target_source,
    )
    if args.proof_pdf:
        pdf = args.proof_pdf.resolve()
        if not pdf.exists():
            raise SystemExit(f"Proof PDF not found: {pdf}")
        target_pdf = case / "proof" / "candidate_proof.pdf"
        if pdf != target_pdf.resolve():
            shutil.copy2(pdf, target_pdf)
        add_frozen_artifact(
            artifacts,
            key="proof_pdf",
            case=case,
            path=target_pdf,
        )
    elif (case / "proof" / "candidate_proof.pdf").exists():
        raise SystemExit(
            "An existing proof/candidate_proof.pdf is not automatically trusted; "
            "pass it explicitly with --proof-pdf"
        )

    for key, relative in STATIC_FREEZE_ARTIFACTS.items():
        add_frozen_artifact(
            artifacts,
            key=key,
            case=case,
            path=case / relative,
        )
    freeze_dependency_cone(case, args.final_claim, artifacts)
    freeze_release_relevant_experiments(case, artifacts)

    freeze = {
        "frozen_at": utc_now(),
        "generation": 1,
        "candidate_kind": args.candidate_kind,
        "final_claim": args.final_claim,
        "artifacts": artifacts,
    }
    if freeze_path.exists():
        old = load_json(freeze_path)
        freeze["generation"] = int(old.get("generation", 0)) + 1
        freeze["supersedes"] = old
    write_json(freeze_path, freeze)

    checkpoint_path = case / "state" / "checkpoint.json"
    checkpoint = load_json(checkpoint_path)
    checkpoint["phase"] = "CANDIDATE_FROZEN"
    checkpoint["active_candidate_claim"] = args.final_claim
    checkpoint["next_actions"] = [
        "Launch independent audit lanes",
        "Do not expose repair discussions to clean-room referee",
    ]
    write_json(checkpoint_path, checkpoint)
    append_event(
        case,
        actor="freeze_candidate.py",
        action="candidate_frozen",
        affected_ids=[args.final_claim],
        evidence_paths=[value["path"] for value in artifacts.values()],
        details={
            "candidate_kind": args.candidate_kind,
            "generation": freeze["generation"],
        },
    )
    print(freeze_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
