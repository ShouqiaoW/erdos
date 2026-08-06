# Computational experimentation and certification

## Valid roles

Computation may:

- falsify a lemma;
- enumerate small structures;
- identify an extremizer;
- suggest an invariant;
- compare asymptotic regimes;
- construct a finite certificate;
- verify an independently proved finite reduction.

It may not silently convert:

```text
verified for n ≤ N
```

into:

```text
true for all n
```

## Reproducibility record

Every experiment records:

- command and arguments;
- working directory;
- source-code hash;
- input hashes;
- interpreter/compiler versions;
- dependency versions when available;
- random seeds;
- start/end time;
- return code;
- stdout/stderr hashes;
- claims tested;
- interpretation.

## Exactness

Prefer:

- integers;
- rationals;
- symbolic algebra with checked assumptions;
- arbitrary precision with explicit error bounds;
- interval arithmetic;
- exact SAT/SMT certificates;
- proof-assistant-checked finite computations.

Floating-point plots are exploratory only.

## Two-program rule

For a certificate on which the final result materially depends:

1. one program generates the certificate;
2. a smaller, independently written checker verifies it.

The checker should have the smallest feasible trust base.

## Negative results

A failed search is not evidence of nonexistence unless the search space is
proved exhaustive and the checker validates the exhaustion.
