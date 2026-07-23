# Release policy

## Status ladder

```text
CONJECTURE
CANDIDATE_PROOF
INTERNALLY_AUDITED_CANDIDATE
PARTIALLY_MACHINE_CHECKED
FULLY_MACHINE_CHECKED
EXTERNALLY_REVIEWED
COMMUNITY_ACCEPTED
```

The automated workflow may assign only
`INTERNALLY_AUDITED_CANDIDATE`.

`FULLY_MACHINE_CHECKED`, `EXTERNALLY_REVIEWED`, and `COMMUNITY_ACCEPTED` require
evidence outside the autonomous workflow and explicit human recording.

Blocked routes, partial lemmas, strategy exhaustion, and resumable checkpoints
are internal research state. They are never terminal release statuses.

## Required candidate package

- frozen source and provenance;
- problem contract and semantic audits;
- affirmative proof source;
- rendered PDF when LaTeX is available;
- claim graph;
- route registry;
- counterexample ledger;
- audit findings and resolutions;
- generation-scoped audit completion records and immutable lane reports;
- verified external-theorem records and application mappings;
- experiment manifest;
- formalization scope manifest;
- prior-art report;
- reproducibility guide;
- gate report.

## Candidate release gate

Pass only when:

- at least the configured eight-hour minimum has elapsed since case creation;
- source hash matches contract;
- contract validator passes;
- final claim has role `final_affirmative` and exactly matches the contract's
  affirmative statement;
- claim graph is acyclic and closed;
- every external dependency is verified with case-local evidence;
- no fatal or major audit finding remains open;
- every standard audit lane independently passed against the current frozen
  candidate generation;
- no frozen contract, ledger, dependency evidence, proof, formalization
  manifest, experiment registry, or audit report changed after its recorded
  hash;
- critical experiments reproduce;
- formalization claims match scope;
- prior-art audit exists;
- release README uses conservative status language.

The packager must re-run the release gate immediately before packaging, reject
symlinked inputs, detect source mutation during archive creation, and exclude
older release archives from the new archive.

## Interrupted-run checkpoints

If a user interruption or external/human-controlled blocker prevents continued
work, preserve:

- strongest proved theorem;
- exact remaining lemma;
- failed route summaries;
- minimal counterexamples;
- experiment data;
- reopen conditions;
- checkpoint.

Do not package or present this checkpoint as a partial theorem, plateau result,
or mathematical terminal response. Resume the research loop when the
interruption clears.
