#!/usr/bin/env python3
"""Shared standard-library utilities for the Erdős Autoresearch Skill."""

from __future__ import annotations

import hashlib
import json
import os
import re
import tempfile
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable

ID_RE = re.compile(r"^(?P<prefix>[A-Z]+)-(?P<number>[0-9]{4,})$")

AUDIT_LANES = [
    "statement",
    "quantifier",
    "edge_case",
    "dependency",
    "external_theorem",
    "counterexample",
    "computation",
    "formalization",
    "clean_room",
    "reproduction",
    "prior_art",
]


class ResearchStateError(RuntimeError):
    """Raised when canonical research state is malformed."""


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def load_json(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise ResearchStateError(f"Missing JSON file: {path}") from exc
    except json.JSONDecodeError as exc:
        raise ResearchStateError(f"Invalid JSON in {path}: {exc}") from exc
    if not isinstance(value, dict):
        raise ResearchStateError(f"Expected JSON object in {path}")
    return value


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = json.dumps(value, indent=2, sort_keys=False, ensure_ascii=False) + "\n"
    atomic_write_text(path, payload)


def atomic_write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp_name = tempfile.mkstemp(prefix=f".{path.name}.", dir=str(path.parent))
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as handle:
            handle.write(text)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(tmp_name, path)
    finally:
        if os.path.exists(tmp_name):
            os.unlink(tmp_name)


def append_jsonl(path: Path, record: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    line = json.dumps(record, sort_keys=True, ensure_ascii=False) + "\n"
    with path.open("a", encoding="utf-8") as handle:
        handle.write(line)
        handle.flush()
        os.fsync(handle.fileno())


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    records: list[dict[str, Any]] = []
    for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        if not line.strip():
            continue
        try:
            item = json.loads(line)
        except json.JSONDecodeError as exc:
            raise ResearchStateError(f"Invalid JSONL in {path}:{line_number}: {exc}") from exc
        if not isinstance(item, dict):
            raise ResearchStateError(f"Expected object in {path}:{line_number}")
        records.append(item)
    return records


def latest_by_id(records: Iterable[dict[str, Any]], id_field: str) -> dict[str, dict[str, Any]]:
    latest: dict[str, dict[str, Any]] = {}
    for record in records:
        identifier = record.get(id_field)
        if isinstance(identifier, str):
            latest[identifier] = record
    return latest


def next_id(path: Path, id_field: str, prefix: str) -> str:
    maximum = 0
    for record in read_jsonl(path):
        identifier = record.get(id_field)
        if not isinstance(identifier, str):
            continue
        match = ID_RE.match(identifier)
        if match and match.group("prefix") == prefix:
            maximum = max(maximum, int(match.group("number")))
    return f"{prefix}-{maximum + 1:04d}"


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def ensure_case(case: Path) -> Path:
    case = case.resolve()
    if not case.exists() or not case.is_dir():
        raise ResearchStateError(f"Case directory does not exist: {case}")
    if not (case / "run_config.json").exists():
        raise ResearchStateError(f"Not an autoresearch case: {case}")
    return case


def split_csv(value: str | None) -> list[str]:
    if not value:
        return []
    return [part.strip() for part in value.split(",") if part.strip()]


def append_event(
    case: Path,
    *,
    actor: str,
    action: str,
    affected_ids: list[str] | None = None,
    evidence_paths: list[str] | None = None,
    details: dict[str, Any] | None = None,
) -> None:
    append_jsonl(
        case / "state" / "events.jsonl",
        {
            "timestamp": utc_now(),
            "actor": actor,
            "action": action,
            "affected_ids": affected_ids or [],
            "evidence_paths": evidence_paths or [],
            "details": details or {},
        },
    )


def relative_to_case(case: Path, path: Path) -> str:
    return str(resolve_case_path(case, path).relative_to(case.resolve()))


def resolve_case_path(
    case: Path,
    value: str | Path,
    *,
    must_exist: bool = False,
    nonempty: bool = False,
) -> Path:
    """Resolve a case-local path and reject traversal or escaping symlinks."""

    case = case.resolve()
    path = Path(value)
    if not path.is_absolute():
        path = case / path
    resolved = path.resolve()
    try:
        resolved.relative_to(case)
    except ValueError as exc:
        raise ResearchStateError(f"Path escapes case directory: {value}") from exc
    if must_exist and (not resolved.exists() or not resolved.is_file()):
        raise ResearchStateError(f"Case-local file does not exist: {value}")
    if nonempty and resolved.stat().st_size == 0:
        raise ResearchStateError(f"Case-local file is empty: {value}")
    return resolved


def has_placeholder(value: Any) -> bool:
    if isinstance(value, str):
        upper = value.upper()
        return "TODO" in upper or "REPLACE_ME" in upper
    if isinstance(value, list):
        return any(has_placeholder(item) for item in value)
    if isinstance(value, dict):
        return any(has_placeholder(item) for item in value.values())
    return False


def materialize_latest(
    source: Path,
    target: Path,
    *,
    id_field: str,
) -> dict[str, dict[str, Any]]:
    latest = latest_by_id(read_jsonl(source), id_field)
    write_json(target, {"records": list(latest.values())})
    return latest
