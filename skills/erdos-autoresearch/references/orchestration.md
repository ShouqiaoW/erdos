# Multi-agent orchestration

## Root responsibilities

The root agent owns:

- contract fidelity;
- route registry;
- claim and obligation state;
- task allocation;
- synthesis decisions;
- audit independence;
- terminal status.

The root should not spend most of its context on raw calculations.

## Independence protocol

During early rounds:

- give scouts the contract, not the favored route;
- avoid showing them other scouts’ summaries;
- use different mechanism prompts;
- require concrete deliverables;
- wait for all assigned scouts before synthesizing.

Cross-pollinate only after routes have exposed:

- core mechanism;
- strongest concrete result;
- key missing lemma;
- falsification history.

## Dynamic allocation

Compute task priority from:

```text
priority =
  obligation severity
+ dependency criticality
+ expected information gain
+ route underrepresentation
+ falsifiability
- duplication
- theorem-strength blocker penalty
- cost
```

Maintain a diversity floor. No family should consume more than half of active
threads unless all alternatives have concrete failure certificates.

## Task envelope

Every delegated task must include:

- case ID;
- frozen statement hash;
- relevant contract sections;
- exact task;
- allowed tools and literature mode;
- concrete required return type;
- forbidden shortcuts;
- output file or response schema;
- time or round budget.

## Saturation

A route is saturated when three independent attempts produce no new mechanism,
claim, counterexample, or sharpened blocker.

Do not equate saturation with falsity. Mark blocked and record reopen conditions.

## Write conflicts

Parallel agents should write only to separate scratch paths. The root or a
single designated state writer promotes accepted artifacts to canonical state.

For computational routes, isolate experiment directories by experiment ID.

## Concurrency

Start below the configured maximum. Increase only when tasks are genuinely
independent. High concurrency is harmful when agents share the same hidden
assumption or compete to edit the same proof.
