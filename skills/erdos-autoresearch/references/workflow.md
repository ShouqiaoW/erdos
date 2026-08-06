# Full workflow and transition gates

## Principle

The workflow is a state machine, not a prose checklist. A later phase cannot
retroactively repair missing source fidelity or contract ambiguity.

## Phase table

| Phase | Name | Required input | Required output | Gate |
|---|---|---|---|---|
| 0 | Initialize | exact source | frozen statement, hash | hash stable |
| 1 | Contract | frozen source | audited contract | two semantic audits |
| 2 | Selection | candidate pool | selected case or expanded pool | equal-budget evidence |
| 3 | Literature isolation | mode | provenance policy | mode recorded |
| 4 | Portfolio | contract | route registry | family diversity |
| 5 | Research rounds | routes | claims and blockers | concrete progress |
| 6 | Claim graph | claims | acyclic dependency graph | no missing deps |
| 7 | Falsification | candidate lemmas | counterexamples/tests | critical lemmas attacked |
| 8 | Computation | falsifiable questions | reproducible experiments | exact scope recorded |
| 9 | Synthesis | closed dependency cone | proof draft | only proved dependencies |
| 10 | Audit | frozen draft | findings ledger | all lanes complete |
| 11 | Repair | findings | repaired or withdrawn claims | downstream regression |
| 12 | Formalization | definitions/lemmas | scope manifest | no overclaim |
| 13 | Prior art | frozen candidate | comparison report | sources traced |
| 14 | Release | all artifacts | gated package | all lanes complete; no fatal/major open |

## Checkpoint discipline

`state/checkpoint.json` should include:

```json
{
  "phase": "AUDIT",
  "round": 9,
  "last_progress_at": "2026-07-23T16:00:00Z",
  "stagnant_rounds": 1,
  "active_candidate_claim": "CLM-0042",
  "next_actions": [
    "Resolve AUD-0017",
    "Re-run EXP-0008 with exact arithmetic"
  ]
}
```

Update the checkpoint after every completed round, candidate freeze, audit wave,
repair wave, strategy reset, or externally interrupted run.

## Phase rollback

Rollback is mandatory when:

- source fidelity changes;
- a definition changes;
- an allowed outcome changes;
- a critical theorem dependency is withdrawn;
- a fatal finding invalidates an earlier dependency cone.

A rollback does not erase subsequent artifacts. Mark them superseded.
