# Proof-contract compiler

The contract converts an informal research question into a testable completion
specification. It is not a new theorem statement.

## Required fields

### Source identity

- authoritative source URI or local origin;
- retrieval date;
- publication/update date when available;
- SHA-256 of frozen statement.

### Canonical statement

Restate the theorem with explicit notation while preserving meaning. Any
clarifying convention absent from the source must be labeled as an
interpretation and audited.

### Definition ledger

Assign IDs to definitions. Include:

- ambient structures;
- finiteness;
- multiplicity conventions;
- empty and degenerate objects;
- measure/probability conventions;
- asymptotic normalization;
- whether constants are absolute or parameter-dependent.

### Quantifier matrix

For each variable record:

- domain;
- quantifier;
- order;
- allowed dependencies;
- fixed versus varying status;
- uniformity requirement.

Example:

```json
{
  "variable": "N",
  "domain": "positive integers",
  "quantifier": "exists",
  "order": 3,
  "depends_on": ["epsilon"],
  "must_be_uniform_in": ["alpha"]
}
```

### Allowed outcomes

Specify exactly what the complete affirmative resolution establishes. Keep the
negative outcome disabled: counterexamples are diagnostic tools for attacking
intermediate claims and routes, not a terminal research outcome. For extremal
problems, include attainment versus infimum/supremum. For asymptotic problems,
include full-sequence versus subsequence and pointwise versus weak convergence.
For graph problems, include connectedness, loops, parallel edges, and
multiplicity.

### Non-solutions

List seductive but insufficient results. Typical categories:

- special subclasses;
- fixed-size computation;
- subsequential convergence;
- heuristic limiting law;
- weaker density;
- changed normalization;
- extra regularity assumptions;
- reduction to an unproved comparable conjecture;
- candidate counterexample without a nonexistence certificate;
- proof of a neighboring statement.

### Traps and regression tests

Every trap needs a check that can be applied to a candidate proof.

Example:

```json
{
  "id": "TRAP-0004",
  "description": "The argument proves convergence only at continuity points.",
  "regression_test": "Locate the step establishing every real threshold c."
}
```

### External theorem policy

For each allowed named theorem class, require:

- exact version;
- hypotheses;
- normalization;
- uniformity;
- whether effectivity is needed;
- source.

## Semantic audits

Auditor A checks symbol-by-symbol fidelity.

Auditor B attempts to construct a model satisfying one statement but not the
other. This is stronger than asking whether the prose “looks equivalent.”

Do not pass the gate if either auditor identifies a possible strengthening,
weakening, quantifier swap, or hidden regularity assumption.
