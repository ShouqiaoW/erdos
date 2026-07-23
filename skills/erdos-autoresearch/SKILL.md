---
name: erdos-autoresearch
description: >
  Run an autonomous, multi-agent, auditable affirmative-proof research workflow
  on a precisely stated Erdős-style open mathematics problem. Use for exact
  statement locking, proof-contract generation, diverse route search,
  intermediate-claim counterexample hunting, computation, claim-graph
  synthesis, hostile proof audit, optional Lean formalization, and conservative
  release packaging. Assume a complete affirmative proof exists as a research
  premise, require at least eight elapsed research hours, and never return a
  partial or plateau result.
---

# Erdős Autoresearch

Operate as the root mathematical research coordinator. Pursue a complete
affirmative proof without relaxing the original statement. Use independent
agents dynamically, preserve failed routes, record durable state, and treat
every result as provisional until it passes the release gate.

Resolve every relative file and script path below from this skill directory.
Run every bundled Python utility through `uv run --no-project`.

## Enforce the research contract

1. Freeze the exact source before reformulating it. Preserve definitions,
   conventions, quantifiers, exceptional cases, source URI, retrieval time, and
   SHA-256.
2. Assume for the research task that a complete affirmative proof exists. Treat
   this only as a search condition; never use it as evidence for a claim.
3. Keep `target_mode` fixed to `prove`. Use counterexamples to falsify
   intermediate claims and routes, never as the terminal outcome.
4. Distinguish proof from evidence. Finite checks, plots, symbolic output,
   agent consensus, and partial formalization do not prove the final theorem.
5. Register every material statement and dependency. Mark a claim `proved`
   only when its complete case-local proof artifact exists.
6. Block a route that ends in a missing lemma of comparable strength. Preserve
   the route, its failed attempts, and its explicit reopen condition.
7. Attack every candidate with independent statement, quantifier, edge-case,
   dependency, theorem-applicability, computation, formalization, clean-room,
   reproduction, and prior-art audits.
8. Never assign `SOLVED`. The maximum automated status is
   `INTERNALLY_AUDITED_CANDIDATE`.
9. Do not return a partial theorem, plateau, no-go result, blocked-route
   summary, or best-effort answer.
10. Require at least eight hours to elapse after case initialization before a
    terminal return. Eight hours is a floor, not a stopping time. Continue
    strategy resets until a complete affirmative candidate passes every gate.
11. If a human or external blocker interrupts the run, persist a resumable
    checkpoint and report an operational interruption, not a mathematical
    result.

## Resolve inputs and defaults

Accept an exact statement, local source file, retrievable URL or problem ID,
candidate-problem directory, or existing case directory.

Resolve:

- `case_id`;
- `selection_mode`: `specified` or `autonomous`;
- `literature_mode`: `benchmark_blind`, `background_only`, or `full_research`;
- computation and formalization permissions;
- a minimum research duration of at least eight hours;
- strategy-reset and concurrency budgets.

Default to `specified`, `background_only`, exact computation where practical,
optional Lean formalization, and an eight-hour minimum.

## Initialize durable state

Keep mutable research state under `cases/<case-id>/`:

```text
source/       contract/     state/        routes/
claims/       experiments/  proof/        audit/
formal/       scratch/      release/      run_config.json
```

Initialize:

```bash
uv run --no-project scripts/init_case.py \
  --case-id <case-id> \
  --problem-file <path> \
  --title "<title>"
```

Never edit a canonical JSONL ledger ad hoc when a bundled script supports the
transition.

## Execute the phase machine

Read `references/workflow.md` for transition and rollback gates.

### 0. Freeze the source

```bash
uv run --no-project scripts/freeze_statement.py \
  --case cases/<case-id> \
  --input <exact-source-file> \
  --source-uri "<authoritative source>"
```

Exit only after the source hash is stable.

### 1. Compile the proof contract

Read:

- `references/proof-contract.md`;
- `references/problem-archetypes.md`;
- `references/failure-modes.md`;
- `references/openai-cdc-example-prompt.txt`;
- `references/openai-cdc-example-notes.md`.

Study the OpenAI CDC prompt as a worked structural exemplar. Preserve its
affirmative-proof premise, persistent search contract, and minimum eight-hour
floor. Replace its theorem-specific content and concurrency count with the
audited case contract.

Create `contract/problem_contract.json` with the exact affirmative outcome,
definitions, quantifier matrix, non-solutions, traps, edge cases, external
theorem policy, and release obligations. Require two independent semantic
audits; do not reveal one auditor's conclusion to the other.

```bash
uv run --no-project scripts/validate_contract.py --case cases/<case-id>
uv run --no-project scripts/compile_research_prompt.py --case cases/<case-id>
```

Resolve every audit disagreement before proof search.

### 2–4. Select, isolate literature, and diversify

For autonomous selection, read `references/problem-selection.md` and use
equal-budget probes. Select on demonstrated information gain, not fame,
attractiveness, or agent confidence.

Read `references/literature-policy.md` and enforce the selected mode. Keep exact
solution information isolated before candidate freeze unless using
`full_research`.

Read `references/orchestration.md` and `references/prompt-patterns.md`. Launch
independent route scouts across genuinely different mechanisms. Require each
scout to return a proved lemma, falsifiable lemma, construction, counterexample,
equivalence, exact formula, or failure certificate.

```bash
uv run --no-project scripts/add_route.py --case cases/<case-id> ...
```

Keep at least one counterexample lane attacking intermediate claims and favored
routes.

### 5–8. Iterate, register, falsify, and compute

Follow the disclosed loop:

```text
attempt → failure → diagnosis → new approach
→ proof draft → adversarial audit → repair
```

Operationalize it as:

```text
attempt → falsification → diagnosis → redirect → lemma proof
→ synthesis → hostile audit → repair
```

At each round, render the dashboard, inspect open obligations, check route
concentration, and generate a bounded queue:

```bash
uv run --no-project scripts/render_dashboard.py --case cases/<case-id>
uv run --no-project scripts/select_tasks.py \
  --case cases/<case-id> \
  --limit <available-independent-slots>
```

Register claims with explicit dependencies:

```bash
uv run --no-project scripts/add_claim.py --case cases/<case-id> ...
uv run --no-project scripts/add_external_theorem.py --case cases/<case-id> ...
uv run --no-project scripts/validate_claim_graph.py --case cases/<case-id>
```

Read `references/research-state.md`. Require case-local evidence for every
proved, refuted, or machine-checked claim. Require an exact statement, source,
hypothesis list, application mapping, and evidence artifact for every verified
external theorem.

For each conjectured lemma, test boundary cases, smallest admissible instances,
hidden dependencies, quantifier reversals, and nearby false strengthenings.
Preserve counterexamples:

```bash
uv run --no-project scripts/record_counterexample.py --case cases/<case-id> ...
```

Read `references/computation.md`. Prefer exact arithmetic and independently
checked certificates. Record experiments:

```bash
uv run --no-project scripts/record_experiment.py --case cases/<case-id> ...
```

Never infer a universal theorem from finite verification without a proved
exhaustive reduction.

### 9. Synthesize an exact affirmative claim

Synthesize only from `proved` or `machine_checked` claims and verified external
theorems. Map every substantive proof step to claim IDs.

Create the final claim directly from the audited affirmative outcome; do not
retype or paraphrase it:

```bash
uv run --no-project scripts/add_claim.py \
  --case cases/<case-id> \
  --affirmative-outcome \
  --status proved \
  --proof-location claims/<proof-artifact> \
  --dependencies <comma-separated-claim-ids>
```

The release machinery rejects any final claim whose role or statement is not
identical to the contract's affirmative outcome.

### 10–13. Freeze, audit, repair, formalize, and check prior art

Read `references/adversarial-audit.md` and
`references/formalization.md`. Freeze the complete candidate:

```bash
uv run --no-project scripts/freeze_candidate.py \
  --case cases/<case-id> \
  --proof-source <candidate.tex> \
  --final-claim <CLM-ID> \
  --candidate-kind affirmative
```

Use fresh agents with minimal discovery-history exposure for each audit lane.
Record every finding:

```bash
uv run --no-project scripts/add_audit_finding.py --case cases/<case-id> ...
```

After resolving all findings, record each required lane against the current
candidate generation and its immutable report:

```bash
uv run --no-project scripts/record_audit.py \
  --case cases/<case-id> \
  --lane <lane> \
  --auditor "<independent auditor identity>" \
  --status pass \
  --report-path audit/<lane-report> \
  --independent
```

Repair every fatal or major finding, update affected dependencies, rerun
experiments, and re-audit the downstream cone. Refreezing creates a new
candidate generation and invalidates all earlier audit completions.

Treat the frozen contract, run configuration, claim and external-theorem
ledgers, final dependency cone, experiments, formalization manifest, and proof
artifacts as immutable. Any change requires a new candidate generation.

Formalize high-risk definitions and lemmas early. State the exact checked scope
in `formal/verification_manifest.json`. Never call the final theorem
machine-checked unless the exact final declaration is accepted within the
declared trust base.

After freeze, perform a full exact-problem prior-art comparison. Distinguish
rediscovery, equivalence, stronger known results, possible novelty, and
unresolved precedence.

### 14. Release only through the gate

Read `references/release-policy.md`. Prepare every required artifact, then run:

```bash
uv run --no-project scripts/release_gate.py \
  --case cases/<case-id> \
  --status INTERNALLY_AUDITED_CANDIDATE \
  --final-claim <CLM-ID>
```

Package only after a pass:

```bash
uv run --no-project scripts/package_release.py --case cases/<case-id>
```

The packager re-runs the gate, rejects symlinked or post-gate-mutated artifacts,
and emits an archive plus a SHA-256 manifest.

## Handle stagnation without returning

Count progress only for a proved or refuted claim, stronger bound, exact
equivalence, concrete counterexample, closed major obligation, weaker
dependency, reproducible certificate, or formalized high-risk lemma.

After the configured stagnant-round threshold:

1. request genuinely new formulations from independent scouts;
2. revisit the decomposition;
3. persist a checkpoint;
4. reset the route portfolio;
5. launch another bounded strategy wave.

Do not treat elapsed time as mathematical evidence. Do not stop merely because
the eight-hour floor has elapsed.

## Map roles to the host agent

Use the host's native independent-agent mechanism when available. Otherwise run
the same task envelopes sequentially with fresh context. Suggested roles:

```text
statement-lock auditor    prior-art librarian    approach scout
lemma prover              counterexample hunter  computationalist
proof synthesizer         hostile referee        quantifier auditor
formalizer                clean-room reproducer
```

Keep the root context focused on the contract, state, dependencies, allocation,
and release decision. Keep raw calculations and failed attempts in separate
agent contexts or case files.
