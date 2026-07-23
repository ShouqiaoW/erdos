# Durable research state

## Canonical ledgers

Use append-only JSONL for events and records that evolve:

- `state/approach_registry.jsonl`
- `state/claims.jsonl`
- `state/obligations.jsonl`
- `state/audit_findings.jsonl`
- `state/audits.jsonl`
- `state/counterexamples.jsonl`
- `state/external_theorems.jsonl`
- `state/events.jsonl`

Use materialized JSON views for current state:

- `state/claim_graph.json`
- `state/checkpoint.json`
- `state/task_queue.json`

## ID namespaces

```text
ROUTE-0001
CLM-0001
OBL-0001
AUD-0001
AUDIT-0001
CTR-0001
EXP-0001
EXT-0001
```

IDs are permanent. Never recycle an ID.

## Claim statuses

- `conjectured`: plausible statement awaiting proof.
- `tested`: survived specified tests but is unproved.
- `proved`: complete stored proof, not machine-checked.
- `machine_checked`: accepted within the declared formal trust base.
- `refuted`: explicit counterexample or contradiction.
- `withdrawn`: no longer asserted for a documented reason.

## Route statuses

- `proposed`
- `active`
- `blocked`
- `refuted`
- `merged`
- `completed`
- `abandoned`

## Obligation statuses

- `open`
- `in_progress`
- `resolved`
- `invalidated`
- `superseded`

## Events

Every mutation should append an event recording:

- timestamp;
- actor or agent role;
- action;
- affected IDs;
- evidence paths;
- previous and new status;
- reason.

## Claim-graph invariant

The dependency graph must be acyclic after ignoring external-theorem nodes.

A final theorem claim cannot be `proved` when any transitive dependency is:

- missing;
- `conjectured`;
- merely `tested`;
- `refuted`;
- `withdrawn`.

The release final claim must have role `final_affirmative` and a statement
identical to `allowed_outcomes.affirmative.statement` in the audited contract.
Create it with `add_claim.py --affirmative-outcome`; do not retype it.

Every external dependency must resolve to a verified `EXT-*` record containing
the exact theorem statement, source URI, hypotheses, application mapping, and a
non-empty case-local evidence artifact.

When a claim becomes refuted, mark every descendant as `withdrawn` or return it
to `conjectured` until repaired.
