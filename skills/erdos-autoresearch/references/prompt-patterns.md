# Specialist task envelopes

Use these as structural prompts, replacing bracketed fields with exact case
content. Require bounded, concrete returns.

## Statement-lock auditor

```text
You are auditing semantic equivalence, not solving the problem.
Compare the frozen source [path/hash] with the proposed contract [path].
List every strengthening, weakening, changed convention, quantifier mismatch,
or new regularity assumption. Attempt to construct a scenario satisfying one
statement but not the other. Return PASS only if no material difference remains.
```

## Approach scout

```text
Work independently on mechanism family [family]. Do not assume the favored
route. Produce at least one concrete lemma, construction, equivalence,
counterexample, exact formula, or failure certificate. State every dependency.
Do not call an unproved global compatibility statement routine.
```

## Lemma prover

```text
Prove or refute exactly claim [CLM-ID]. You may use only the listed proved
dependencies and declared external theorems. Search for counterexamples before
writing a proof. Return one of: complete proof, explicit counterexample, or exact
remaining obligation.
```

## Counterexample hunter

```text
Attack [CLM-ID]. Focus on smallest cases, boundary parameters, repeated objects,
degenerate structures, quantifier reversals, and near-extremal examples. Return
machine-readable counterexamples where possible and explain precisely which
hypothesis or conclusion fails.
```

## Computationalist

```text
Design the smallest exact experiment that discriminates among [hypotheses].
Prefer rational/integer arithmetic. Record command, versions, hashes, and seeds.
Separate certificate generation from checking. State exactly what the output
does and does not prove.
```

## Proof synthesizer

```text
Construct a proof draft only from claims marked proved or machine_checked and
verified external theorems. Map each substantive paragraph to claim IDs. Do not
hide gaps with phrases such as standard, routine, clearly, or similarly.
```

## Hostile referee

```text
Assume the candidate may be wrong. Read only the frozen statement, contract,
proof, and dependency list. Locate the first fatal gap if one exists. Check
statement fidelity, theorem hypotheses, circularity, edge cases, and exact
quantifiers. Do not repair the proof while reviewing it.
```

## Quantifier auditor

```text
Extract every quantified assertion in the proof and compare it with the
contract’s quantifier matrix. Check parameter dependencies and uniformity.
Return a table of proof locations, quantifiers used, and any mismatch.
```

## Clean-room reproducer

```text
Reconstruct the core argument from the theorem statement and declared lemmas
without copying the proof’s prose. Report which transitions can be independently
derived and which require hidden intuition or an unstated lemma.
```

## Prior-art librarian

```text
Follow literature mode [mode]. Keep discovery information isolated as required.
After candidate freeze, compare each central claim and mechanism with exact prior
art. Distinguish rediscovery, equivalence, stronger known results, possible
novelty, and unresolved precedence.
```
