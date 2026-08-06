#!/usr/bin/env python3
"""Compile the audited problem contract into a problem-specific Codex research goal."""

from __future__ import annotations

import argparse
from pathlib import Path
from typing import Any

from _common import atomic_write_text, ensure_case, load_json
from validate_contract import validate


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--allow-draft", action="store_true")
    return parser.parse_args()


def bullets(items: list[Any], *, empty: str = "_None specified._") -> str:
    if not items:
        return empty
    lines: list[str] = []
    for item in items:
        if isinstance(item, str):
            lines.append(f"- {item}")
        elif isinstance(item, dict):
            identifier = item.get("id")
            description = (
                item.get("description")
                or item.get("definition")
                or item.get("statement")
                or str(item)
            )
            prefix = f"`{identifier}` — " if identifier else ""
            lines.append(f"- {prefix}{description}")
        else:
            lines.append(f"- {item}")
    return "\n".join(lines)


def outcome_block(name: str, outcome: dict[str, Any]) -> str:
    if not outcome.get("enabled"):
        return f"### {name}\n\n_Disabled by the audited contract._"
    return (
        f"### {name}\n\n"
        f"{outcome.get('statement', '')}\n\n"
        f"Required obligations:\n\n{bullets(outcome.get('obligations', []))}"
    )


def main() -> int:
    args = parse_args()
    case = ensure_case(args.case)
    report = validate(case, allow_draft=args.allow_draft)
    if not report["valid"]:
        raise SystemExit(
            "Contract validation failed; refusing to compile research prompt:\n- "
            + "\n- ".join(report["errors"])
        )
    contract = load_json(case / "contract" / "problem_contract.json")
    config = load_json(case / "run_config.json")
    output = args.output or case / "contract" / "research_goal.md"

    quantifier_lines = []
    for item in contract.get("quantifier_matrix", []):
        if not isinstance(item, dict):
            continue
        quantifier_lines.append(
            "- `{variable}` over {domain}: `{quantifier}` at order {order}; "
            "depends on {depends}; uniform in {uniform}".format(
                variable=item.get("variable", "?"),
                domain=item.get("domain", "?"),
                quantifier=item.get("quantifier", "?"),
                order=item.get("order", "?"),
                depends=item.get("depends_on", []),
                uniform=item.get("must_be_uniform_in", []),
            )
        )

    outcomes = contract.get("allowed_outcomes", {})
    text = f"""# Autonomous research goal — {config.get("title")}

## Immutable identity

- Case ID: `{config.get("case_id")}`
- Frozen source SHA-256: `{contract.get("source", {}).get("sha256")}`
- Literature mode: `{config.get("literature_mode")}`
- Target mode: `prove`
- Minimum research duration: `{config.get("budget", {}).get("minimum_research_hours", 8)}` hours

Do not change the statement, definitions, quantifiers, normalization, admissible
class, or completion criteria below.

Assume for purposes of this research task that a complete affirmative proof
exists. This is a search condition, not evidence for any claim or missing step.

## Exact canonical statement

{contract.get("canonical_statement")}

## Definitions

{bullets(contract.get("definitions", []))}

## Quantifier and dependence matrix

{chr(10).join(quantifier_lines) if quantifier_lines else "_No quantified variables recorded._"}

## Complete outcomes

{outcome_block("Affirmative resolution", outcomes.get("affirmative", {}))}

Counterexamples are diagnostic tools for falsifying intermediate claims and
routes. They are not a terminal outcome for this affirmative-proof task.

## Results that do not count

{bullets(contract.get("non_solutions", []))}

## Problem-specific traps

{bullets(contract.get("traps", []))}

## Edge and degenerate cases

{bullets(contract.get("edge_cases", []))}

## Research policy

- Follow the loop: attempt → failure → diagnosis → new approach → proof draft
  → adversarial audit → repair.
- Begin with a diverse portfolio of genuinely different mathematical mechanisms.
- Preserve independence during early rounds; do not tell most scouts the favored route.
- Maintain explicit route, claim, obligation, counterexample, and audit ledgers.
- Keep a counterexample lane attacking intermediate claims and favored routes.
- Search aggressively for counterexamples to every proposed lemma.
- Mark a route blocked when it ends at an unproved statement of comparable strength.
- Reopen blocked routes only after a materially new mechanism appears.
- Treat finite computation as evidence unless connected to a proved exhaustive reduction.
- Require concrete lemmas, constructions, equations, certificates, or counterexamples.
- Synthesize only from proved or machine-checked claims and verified external theorems.
- Create the terminal claim from the contract with `add_claim.py --affirmative-outcome`;
  never retype or paraphrase the exact affirmative statement.
- Freeze every candidate proof before independent adversarial audit.
- Complete every required audit lane against the current frozen generation and
  preserve each immutable report hash.
- Do not call the problem solved. The maximum internal status is
  `INTERNALLY_AUDITED_CANDIDATE`.

## Literature policy

Follow `{config.get("literature_mode")}` exactly. Record all external theorem
statements, hypotheses, sources, and where they enter the claim graph.

## Return conditions

Spend at least the configured eight-hour minimum before considering a terminal
return. Return only when the exact affirmative outcome survives all release
gates as `INTERNALLY_AUDITED_CANDIDATE`. Do not return a partial theorem,
plateau, blocked-route summary, no-go result, or best-effort answer. Persist
checkpoints internally and continue with a materially new strategy wave.
"""
    atomic_write_text(output, text)
    print(output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
