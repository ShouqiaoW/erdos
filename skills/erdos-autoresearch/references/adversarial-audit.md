# Adversarial audit

## Audit lanes

### Statement fidelity

Does the draft prove exactly one allowed outcome in the contract?

### Quantifiers and uniformity

Check order, allowed dependencies, hidden compactness, limit interchange, and
full-sequence versus subsequence claims.

### Edge cases

Check empty, degenerate, repeated, boundary, disconnected, rational, singular,
zero-measure, or low-dimensional cases as relevant.

### Dependency strength

Identify any lemma equivalent or comparable in strength to the original
problem. Check circularity through renamed statements.

### External theorem applicability

For every named theorem, verify the exact hypotheses and normalization.

### Counterexample search

Attack every new lemma, not only the final theorem.

### Computational audit

Reproduce commands and inspect whether code verifies the claimed proposition.

### Formalization scope

Compare prose claims to the exact theorem objects checked.

### Clean-room referee

Give a fresh referee only:

- frozen source;
- contract;
- proof draft;
- declared external dependencies.

Hide discovery notes and intended repairs.

### Independent reproducer

Ask a separate agent to reconstruct the key proof steps without copying the
draft’s prose. Failure to reproduce is a signal, not automatically a refutation.

### Prior art

Compare the frozen candidate's central claims and mechanism with exact-problem
literature. Distinguish rediscovery, equivalent known arguments, stronger known
results, possible novelty, and unresolved precedence.

## Severity

- `fatal`: invalidates the claimed outcome.
- `major`: leaves a substantive theorem obligation open.
- `minor`: repairable local gap not currently known to alter the result.
- `editorial`: clarity or presentation only.

All fatal and major findings must be resolved or the candidate status withdrawn.

## Lane completion

After resolving findings, write a dedicated non-empty report for each lane and
record it with `scripts/record_audit.py --independent`. A completion record is
valid only for the current candidate generation and final claim. The release
gate verifies the report hash.

Do not use a finding record as evidence that a lane completed. Refreezing the
candidate invalidates every completion record from the previous generation.

## Repair standard

A repair is accepted only when:

- the amended claim is explicit;
- dependencies are updated;
- previous counterexamples are re-run;
- downstream claims are re-audited;
- a fresh referee does not rely on the repair discussion.
