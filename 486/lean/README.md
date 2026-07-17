# Erdős Problem 486 in Lean 4

This directory contains a complete Lean 4/mathlib formalization of a
negative solution to [Erdős Problem 486](https://www.erdosproblems.com/486).
The accompanying mathematical write-up is
[`../paper.tex`](../paper.tex).

The formal statement keeps the original data and strict activation condition:

- a set of positive moduli `A ⊆ ℕ` (represented by `0 ∉ A`);
- arbitrary residue sets `X n ⊆ ZMod n` for `n ∈ A`;
- modulus `n` constrains an integer `m` only when `n < m`.

The construction gives one fixed infinite congruence system whose survivor
set has no logarithmic density. More precisely, its logarithmic averages have

```text
liminf ≤ 177 / 200 < 49 / 50 ≤ limsup.
```

## Final Lean theorems

The unconditional exported theorems are in
[`Erdos486/Main.lean`](Erdos486/Main.lean):

```lean
Erdos486.erdos486_quantitativeCounterexample :
  Erdos486.QuantitativeCounterexample

Erdos486.erdos486_negative :
  ¬ Erdos486.Erdos486Assertion
```

The exact problem statement is defined in
[`Erdos486/Statement.lean`](Erdos486/Statement.lean).

## Build

The project pins Lean `v4.27.0` and mathlib `v4.27.0`. With `elan` installed,
run from this Lean package directory (`486/lean` in the parent repository):

```bash
lake exe cache get
lake build
```

The complete build succeeds with warnings treated as errors. The source has
no `sorry`, `admit`, custom axioms, or proof placeholders. `#print axioms` for
both final theorems reports only Lean/mathlib's standard foundations:
`propext`, `Classical.choice`, and `Quot.sound`.

GitHub Actions runs the same build automatically on every push and pull
request.

## Structure

- `Erdos486/Statement.lean`: exact statement and quantitative counterexample.
- `Erdos486/Periodic.lean`, `Erdos486/LogBounds.lean`: logarithmic-density and
  periodic-recovery machinery.
- `Erdos486/BiasedSkeleton.lean`, `Erdos486/BiasedColoring.lean`: arithmetic
  block construction.
- `Erdos486/BiasedFiniteBlock.lean`: exact finite four-colouring averaging and
  deterministic small-footprint block.
- `Erdos486/BiasedRecovery.lean`: recovery for every finite collection of
  installed blocks, preserving strict activation.
- `Erdos486/Global.lean`: gliding-hump construction and oscillating averages.
- `Erdos486/BiasedInterface.lean`, `Erdos486/Main.lean`: concrete assembly and
  final theorem.

The manuscript's finite probabilistic step is replaced in Lean by a stronger
exact finite-enumeration argument. It proves the same required block
properties without adding assumptions or relying on measure-theoretic
probability.

## Relation to Formal Conjectures

The current
[`FormalConjectures/ErdosProblems/486.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/486.lean)
encodes a simplified statement that does not include the set `A` or the strict
activation condition `n < m`. This repository therefore defines and proves the
exact statement independently rather than filling that template directly.
