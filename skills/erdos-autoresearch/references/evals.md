# Evaluating the Skill

The primary objective is to minimize false proof claims while preserving useful
research output.

## Blinded evaluation set

Include:

- solved problems with solutions withheld;
- currently open problems;
- problems with known partial results;
- one-quantifier variants;
- deliberately malformed statements;
- problems where finite evidence is misleading;
- arguments with planted circularity;
- proofs with hidden theorem-hypothesis failures;
- counterexample problems;
- problems whose answer depends on a boundary convention.

## Metrics

- exact statement fidelity;
- correct proof rate;
- false proof rate;
- correct abstention or blocking rate;
- counterexample discovery rate;
- gap localization quality;
- claim-graph completeness;
- experiment reproducibility;
- formalization-scope accuracy;
- prior-art contamination rate;
- compute and token cost per verified outcome.

## Hard failures

Any of these should score zero for the run:

- proves a strengthened or weakened statement without disclosure;
- calls a tested claim proved;
- ignores a fatal audit finding;
- claims full formalization from partial Lean files;
- labels an internal candidate solved;
- deletes a discovered counterexample;
- cites a theorem whose hypotheses are false in the application.
