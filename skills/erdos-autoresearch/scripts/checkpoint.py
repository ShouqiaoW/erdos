#!/usr/bin/env python3
"""Update the durable phase/round checkpoint without hand-editing JSON."""

from __future__ import annotations

import argparse
from pathlib import Path

from _common import append_event, ensure_case, load_json, split_csv, utc_now, write_json


PHASES = [
    "INITIALIZED",
    "STATEMENT_FROZEN",
    "CONTRACT_DRAFTED",
    "CONTRACT_AUDITED",
    "SELECTED",
    "PORTFOLIO_ACTIVE",
    "RESEARCH",
    "SYNTHESIS",
    "CANDIDATE_FROZEN",
    "AUDIT",
    "REPAIR",
    "FORMALIZATION",
    "PRIOR_ART",
    "RELEASE_GATE",
    "TERMINAL",
]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", type=Path, required=True)
    parser.add_argument("--phase", choices=PHASES)
    parser.add_argument("--round", type=int)
    parser.add_argument("--stagnant-rounds", type=int)
    parser.add_argument("--active-candidate-claim")
    parser.add_argument("--next-actions")
    parser.add_argument("--progress", action="store_true")
    parser.add_argument("--actor", default="root")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    case = ensure_case(args.case)
    path = case / "state" / "checkpoint.json"
    checkpoint = load_json(path)
    if args.phase is not None:
        checkpoint["phase"] = args.phase
    if args.round is not None:
        checkpoint["round"] = args.round
    if args.stagnant_rounds is not None:
        checkpoint["stagnant_rounds"] = args.stagnant_rounds
    if args.active_candidate_claim is not None:
        checkpoint["active_candidate_claim"] = args.active_candidate_claim or None
    if args.next_actions is not None:
        checkpoint["next_actions"] = split_csv(args.next_actions)
    if args.progress:
        checkpoint["last_progress_at"] = utc_now()
        checkpoint["stagnant_rounds"] = 0
    write_json(path, checkpoint)
    append_event(
        case,
        actor=args.actor,
        action="checkpoint_updated",
        affected_ids=[args.active_candidate_claim] if args.active_candidate_claim else [],
        details=checkpoint,
    )
    print(path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
