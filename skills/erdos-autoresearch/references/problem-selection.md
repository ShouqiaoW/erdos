# Autonomous problem selection

Problem selection creates severe hidden selection bias. Treat it as an
experiment with a fixed protocol.

## Stage 1 — Structural triage

Score each candidate from 0–4 on:

- statement precision;
- number of independent formulations;
- availability of falsifiable intermediate claims;
- usefulness of exact small-instance computation;
- formalizability of definitions;
- distance from major open conjectures;
- tractability of the literature boundary;
- likelihood that partial progress can be stated cleanly.

Penalize:

- ambiguity;
- dependence on opaque unpublished machinery;
- routes that immediately reduce to famous conjectures;
- no plausible counterexample search;
- inability to distinguish novelty from rediscovery;
- problem statements that appear stale or incorrectly transcribed.

Do not use social prominence as a positive mathematical feature.

## Stage 2 — Equal-budget probe tournament

Give each survivor the same:

- number of independent scouts;
- reasoning level;
- tool access;
- maximum rounds;
- output requirements.

A probe earns evidence only for:

- a complete nontrivial lemma proof;
- a concrete counterexample;
- a proved exact equivalence;
- a new finite decomposition with a generalization mechanism;
- a reproducible computation that falsifies a natural route;
- a precise blocker demonstrating why a route is not viable.

Model confidence and elegant prose earn no points.

## Selection score

Use a weighted score:

```text
verified information gain        35%
route diversity                  15%
falsifiability                   15%
dependency strength              15%
formal/computational leverage    10%
literature separability          10%
```

Subtract a large penalty when the best route depends on a theorem-strength
missing lemma.

## Decision

Select the problem with the best verified information-gain profile, not the
highest predicted chance of success.

When no candidate passes the threshold, expand the candidate pool or run
another equal-budget probe wave. Do not issue `NO_GO` as a terminal research
result.
